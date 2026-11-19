/* stroke.js — détection des phases d'un putt à partir de l'accélération linéaire (sans gravité) d'un téléphone fixé sur le putter.
 *
 * Phases : settle (stabilisation après la remise à zéro) → address → back (backswing) → fwd (forward swing) → follow (après l'impact) → done (fin de swing).
 *
 * Principe :
 *  - la première poussée soutenue après l'adresse est le recul : son sens définit l'axe du coup (avant = sens opposé), quelle que soit la façon dont le téléphone est fixé ;
 *  - l'accélération signée sur cet axe est intégrée depuis le début du geste (le biais capteur est mesuré à l'adresse) → vitesse de la tête ;
 *  - sommet du backswing = la vitesse remonte à zéro ; impact = pic de vitesse avant (affiné par le choc sur l'accélération brute s'il est net) ;
 *  - fin de swing = la main s'est immobilisée après l'impact.
 * Les temps entrants sont en ms (horloge du téléphone), les temps internes en secondes.
 *
 * Deux modes d'entrée :
 *  - push(t, ax, ay, az)                   : accélération linéaire (gravité déjà retirée par le téléphone) ;
 *  - push(t, ax, ay, az, gx, gy, gz)       : accélération BRUTE (gravité incluse, m/s²) + gyroscope (rad/s). Le gyro suit l'orientation, ce qui permet
 *    (1) de retirer la gravité sans fuite quand le putter s'incline, (2) de détecter calme / départ / sommet par la rotation (sensible, sans dérive),
 *    (3) d'obtenir la vitesse de la tête par v = L·ω (une seule intégration, donc beaucoup moins de dérive) ; L (bras de levier) est ajusté
 *    sur chaque putt en comparant avec la vitesse issue de l'accélération.
 */
(function (root) {
'use strict';

const DEF = {
  tau: 0.020,        // lissage de l'accélération pour l'intégration (s)
  tau2: 0.060,       // lissage plus fort pour détecter calme / départ / fin : les gestes lents sont faibles mais durables (s)
  quietThr: 0.15,    // accélération « au repos » (m/s²)
  startThr: 0.10,    // seuil de départ minimal du backswing (m/s²) ; adaptatif : max(startThr, 5 × bruit mesuré à l'adresse)
  settle: 0.8,       // durée mini de stabilisation après la remise à zéro (s)
  quietNeed: 0.3,    // durée de calme nécessaire pour être « prêt » (s)
  trigger: 0.03,     // durée au-dessus du seuil pour déclencher (s)
  lockDelay: 0.08,   // délai mini avant de fixer l'axe du coup (s)
  vTrig: 0.025,      // départ aussi déclenché par la vitesse intégrée (filtrée passe-haut) : détecte les gestes lents (m/s)
  tauL: 1.2,         // constante de fuite de cette vitesse (s)
  lockV: 0.04,       // vitesse mini (intégrée) pour fixer l'axe : assez de mouvement pour que le sens soit fiable (m/s)
  lockMax: 1.0,      // sans cette vitesse après ce délai, ce n'est pas un coup (s)
  minBackV: 0.03,    // vitesse de recul mini pour valider un backswing (m/s)
  minVmax: 0.08,     // vitesse avant mini pour valider un forward swing (m/s)
  maxBack: 5.0, maxFwd: 3.0, maxFollow: 2.5, // temporisations (s)
  endQuiet: 0.25,    // calme nécessaire pour déclarer la fin du swing (s)
  maxIdleLog: 1500,  // échantillons gardés au repos
  lever: 1.2,        // bras de levier pivot → téléphone (m), valeur de départ ; ajusté à chaque putt (mode gyro)
  gStill: 0.03,      // rotation « immobile » (rad/s) : le téléphone ne tourne pas, la gravité peut être recalée sur l'accéléromètre
  gTrig: 0.025,      // départ déclenché par la rotation (rad/s), adaptatif : max(gTrig, 5 × bruit mesuré à l'adresse)
  lockAng: 0.02      // angle mini (rad) pour fixer l'axe de rotation du coup
};
const dot = (a, f) => a[0] * f[0] + a[1] * f[1] + a[2] * f[2];

function StrokeDetector(opts) { this.o = Object.assign({}, DEF, opts || {}); this.lever = this.o.lever; this.gbKeep = null; this.reset(); }
const P = StrokeDetector.prototype;

P.reset = function () {
  this.state = 'settle';
  this.T = []; this.R = [[], [], []]; this.A = []; this.M = []; this.V = []; this.W = []; this.Wm = []; this.U = [];
  this.AL = null; this.YW = null; this.nRef = null;
  this.hasGyro = false; this.G = null; this.gb = [0, 0, 0]; this.sw = [0, 0, 0]; this.sw2 = [0, 0, 0]; this.sw3 = [0, 0, 0]; this.sa = [0, 0, 0]; this.gm = null; this.noiseW = 0.005; this.gOver = 0; this.nHat = [0, 1, 0]; this.angLen = 0; this.leverFit = null;
  this.s = null; this.s2 = null; this.bias = [0, 0, 0]; this.tPrev = null; this.tReset = null;
  this.quietT = 0; this.overT = 0; this.noise = 0.05; this.vh = [0, 0, 0]; this.vmCur = 0; this.noiseV = 0.01; this.vOver = 0; this.tAddr = 0;
  this.t0 = this.tTop = this.tImp = this.tEnd = null;
  this.i0 = this.iTop = this.iImp = this.iEnd = -1;
  this.f = null; this.locked = false; this.metrics = null; this.shock = false;
  this.aborts = 0; this.note = ''; this.thr0 = 0; this.vLen = 0; this.rKeep = 1; this.sm = null; this.sInfo = null; this._w3 = 0;
  this.vmin = 0; this.vmax = 0; this.tVmax = 0; this.reached = false; this.lockAt = 0;
};

/* assouplissement des critères de calme : au bout de 3 s de stabilisation sans y arriver, les seuils montent progressivement (jusqu'à ×3).
   Un putter tenu à la main bouge toujours un peu ; mieux vaut accepter ce niveau d'agitation (les seuils de départ s'y adaptent) que ne jamais se déclarer prêt. */
P._relax = function (t) {
  const rt = this.state === 'settle' && this.tReset !== null ? Math.min(3, Math.max(1, 1 + (t - this.tReset - 3) / 3)) : 1;
  return Math.max(this.rKeep, rt);
};
/* avancement de la stabilisation (0..1) et facteur limitant, pour la jauge */
P.settleProgress = function () {
  if (this.state !== 'settle') return this.state === 'address' ? 1 : 0;
  const s = this.sInfo; if (!s) return 0;
  return Math.max(0, Math.min(1, Math.min(s.el / s.need, s.quietT / s.quietNeed)));
};
P.settleLimit = function () {                               // ce qui empêche d'avancer : 'gyro' (le putter tourne), 'acc' (il accélère), 'time' (juste attendre), ''
  const s = this.sInfo; if (this.state !== 'settle' || !s) return '';
  if (s.gyR > 1) return 'gyro'; if (s.accR > 1) return 'acc'; return s.quietT < s.quietNeed || s.el < s.need ? 'time' : '';
};

P.thr = function () { return Math.max(this.o.startThr, 5 * this.noise); };

P.push = function (tMs, x, y, z, gx, gy, gz) {
  if (this.state === 'done') return this.state;
  const o = this.o, t = tMs / 1000, first = this.tPrev === null;
  let dt = 0;
  const gyro = gx !== undefined && gy !== undefined && gz !== undefined;
  if (first) this.hasGyro = gyro;
  let wmag = 0, wstill = true;
  if (this.hasGyro) {                                       // mode brut : suivi de la gravité par le gyro, puis accélération linéaire
    if (first) { this.G = [x, y, z]; this.gb = this.gbKeep ? this.gbKeep.slice() : [gx, gy, gz]; this.gm = [gx, gy, gz]; this.sw = [0, 0, 0]; this.sw2 = [0, 0, 0]; this.sw3 = [0, 0, 0]; this.sa = [x, y, z]; }
    else if (t - this.tPrev <= 0) return this.state;
    const d0 = first ? 0 : t - this.tPrev, gb = this.gb, G = this.G;
    const w = [gx - gb[0], gy - gb[1], gz - gb[2]];
    const kw = first ? 1 : 1 - Math.exp(-d0 / 0.02), kw2 = first ? 1 : 1 - Math.exp(-d0 / 0.05), ka = first ? 1 : 1 - Math.exp(-d0 / 0.06);
    const kw3 = first ? 1 : 1 - Math.exp(-d0 / 0.15);
    for (let j = 0; j < 3; j++) { this.sw[j] += (w[j] - this.sw[j]) * kw; this.sw2[j] += (w[j] - this.sw2[j]) * kw2; this.sw3[j] += (w[j] - this.sw3[j]) * kw3; this.sa[j] += ([x, y, z][j] - this.sa[j]) * ka; }
    wmag = Math.hypot(this.sw2[0], this.sw2[1], this.sw2[2]);
    // la gravité, vue dans le repère du téléphone, tourne avec lui : dG/dt = −ω × G (intégrée avec la rotation exacte autour de ω)
    if (d0 > 0) { const wn = Math.hypot(w[0], w[1], w[2]), ang = wn * d0;
      if (ang > 1e-9) { const ux = w[0] / wn, uy = w[1] / wn, uz = w[2] / wn, c = Math.cos(ang), s = Math.sin(-ang), cr = [uy * G[2] - uz * G[1], uz * G[0] - ux * G[2], ux * G[1] - uy * G[0]], dd = ux * G[0] + uy * G[1] + uz * G[2];
        for (let j = 0; j < 3; j++) G[j] = G[j] * c + cr[j] * s + [ux, uy, uz][j] * dd * (1 - c); } }
    const resting0 = this.state === 'settle' || this.state === 'address';
    // immobile = la rotation (lissée sur ~0,15 s) NE VARIE PAS par rapport à sa moyenne lente (0,5 s) et reste petite. On juge la variation, pas le niveau :
    // un biais de gyro mal estimé est un décalage stable, qui ne doit pas empêcher d'apprendre ce biais (sinon : interblocage).
    if (d0 > 0) { const kg5 = 1 - Math.exp(-d0 / 0.5); this.gm[0] += (gx - this.gm[0]) * kg5; this.gm[1] += (gy - this.gm[1]) * kg5; this.gm[2] += (gz - this.gm[2]) * kg5; }
    const swr = [this.sw3[0] + gb[0], this.sw3[1] + gb[1], this.sw3[2] + gb[2]], w3 = Math.hypot(swr[0] - this.gm[0], swr[1] - this.gm[1], swr[2] - this.gm[2]), rr0 = this._relax(t); this._w3 = w3;
    wstill = w3 < o.gStill * rr0 && Math.hypot(swr[0], swr[1], swr[2]) < 0.25;          // seuil assoupli si la stabilisation traîne
    if (resting0 && wstill && d0 > 0) {                    // immobile : le biais du gyro et la gravité sont recalés (vite juste après la remise à zéro, ou si l'écart est grand)
      const fast = this.tReset === null || t - this.tReset < 1.5, gerr = Math.hypot(this.sa[0] - G[0], this.sa[1] - G[1], this.sa[2] - G[2]);
      const kb = 1 - Math.exp(-d0 / (fast ? 0.3 : 1.5)), kg = 1 - Math.exp(-d0 / ((fast || gerr > o.quietThr) ? 0.4 : 2.0));
      for (let j = 0; j < 3; j++) { gb[j] += this.sw2[j] * kb; G[j] += (this.sa[j] - G[j]) * kg; }
      this.gbKeep = gb.slice();          // sw2 = gyro lissé − biais : l'écart restant est du biais
      if (w3 < o.gStill && Math.hypot(this.sw3[0], this.sw3[1], this.sw3[2]) < 2 * o.gStill) { this.noiseW += (Math.min(wmag, 2.5 * this.noiseW + 0.004) - this.noiseW) * (1 - Math.exp(-d0 / 1.0)); this.noiseW = Math.min(this.noiseW, 0.02); }
    }
    x = x - G[0]; y = y - G[1]; z = z - G[2];
  }
  if (first) { this.tReset = t; this.s = [x, y, z]; this.s2 = [x, y, z]; this.bias = [x, y, z]; }
  else { dt = t - this.tPrev; if (dt <= 0) return this.state; }
  this.tPrev = t;
  const k = first ? 1 : 1 - Math.exp(-dt / o.tau), k2 = first ? 1 : 1 - Math.exp(-dt / o.tau2), s = this.s, s2 = this.s2, b = this.bias;
  s[0] += (x - s[0]) * k; s[1] += (y - s[1]) * k; s[2] += (z - s[2]) * k;
  s2[0] += (x - s2[0]) * k2; s2[1] += (y - s2[1]) * k2; s2[2] += (z - s2[2]) * k2;
  let a = [s[0] - b[0], s[1] - b[1], s[2] - b[2]], mag = Math.hypot(s2[0] - b[0], s2[1] - b[1], s2[2] - b[2]);   // mag : version fortement lissée (détection)
  const resting = this.state === 'settle' || this.state === 'address';
  const el = first ? 0 : t - this.tReset, rr = this._relax(t);
  const vq = this.vmCur !== undefined ? this.vmCur : 0;
  // « immobile » : avec le gyro, c'est lui qui le dit (un putt fait toujours tourner le téléphone) ; sans gyro, la vitesse intégrée doit rester faible
  // (sans gyro, un décalage constant est indiscernable d'un geste très lent : si la stabilisation traîne (assouplissement ≥ ×1,5, soit > 4,5 s), on le traite comme du biais)
  const still = this.hasGyro ? wstill : (el < 1.5 || vq < (1.5 * this.noiseV + 0.006) * rr || rr >= 1.5);
  // « stable » = le signal ne varie pas (même s'il est décalé : un décalage stable est du biais, pas un mouvement) ; évite le blocage quand le capteur lit un décalage > seuil
  if (!this.sm) this.sm = s2.slice(); else { const ks = 1 - Math.exp(-dt / 0.6); this.sm[0] += (s2[0] - this.sm[0]) * ks; this.sm[1] += (s2[1] - this.sm[1]) * ks; this.sm[2] += (s2[2] - this.sm[2]) * ks; }
  const stable = Math.hypot(s2[0] - this.sm[0], s2[1] - this.sm[1], s2[2] - this.sm[2]) < o.quietThr * rr;
  if (resting && stable && still && dt > 0) {            // biais capteur et bruit : appris pendant le calme ; jamais en plein geste
    const kb = 1 - Math.exp(-dt / ((el < 1.5 || mag > o.quietThr * rr) ? 0.4 : 2.5));      // vite tant qu'un décalage subsiste
    b[0] += (s2[0] - b[0]) * kb; b[1] += (s2[1] - b[1]) * kb; b[2] += (s2[2] - b[2]) * kb;
    a = [s[0] - b[0], s[1] - b[1], s[2] - b[2]]; mag = Math.hypot(s2[0] - b[0], s2[1] - b[1], s2[2] - b[2]);
    if (mag < o.quietThr * rr) this.noise += (Math.min(mag, 2.5 * this.noise + 0.02) - this.noise) * (1 - Math.exp(-dt / 0.5));
  }
  if (resting && dt > 0) {                                 // vitesse intégrée à fuite : un geste lent est faible en accélération mais bien visible en vitesse
    const dk = Math.exp(-dt / o.tauL), vh = this.vh; vh[0] = vh[0] * dk + a[0] * dt; vh[1] = vh[1] * dk + a[1] * dt; vh[2] = vh[2] * dk + a[2] * dt;
    const vm = Math.hypot(vh[0], vh[1], vh[2]); this.vmCur = vm;
    if (t - this.tReset >= 1.5 && mag < o.quietThr * rr && vm < 1.5 * this.noiseV + 0.003) this.noiseV = Math.min(0.02, this.noiseV + (vm - this.noiseV) * (1 - Math.exp(-dt / 1.0)));   // ne peut pas « apprendre » un mouvement lent comme du bruit
  }
  if (resting && this.T.length > o.maxIdleLog) {           // au repos : fenêtre glissante
    const c = 500; this.T.splice(0, c); this.R.forEach(r => r.splice(0, c)); this.A.splice(0, c); this.M.splice(0, c); this.V.splice(0, c); this.W.splice(0, c); this.Wm.splice(0, c); this.U.splice(0, c);
  }
  this.T.push(t); this.R[0].push(x); this.R[1].push(y); this.R[2].push(z); this.A.push(a); this.M.push(mag); this.V.push(0);
  this.W.push(this.hasGyro ? this.sw.slice() : [0, 0, 0]); this.Wm.push(wmag);
  { let u = [0, 0, 0]; if (this.hasGyro) { const gn = Math.hypot(this.G[0], this.G[1], this.G[2]) || 1; u = [this.G[0] / gn, this.G[1] / gn, this.G[2] / gn]; } this.U.push(u); }   // « haut » vu dans le repère du téléphone
  const i = this.T.length - 1;

  switch (this.state) {
    case 'settle':
      this.quietT = mag < o.quietThr * rr && wstill ? this.quietT + dt : 0;
      this.sInfo = { el, need: o.settle, quietT: this.quietT, quietNeed: o.quietNeed, accR: mag / (o.quietThr * rr), gyR: this.hasGyro ? this._w3 / (o.gStill * rr) : 0, relax: rr };
      if (el >= o.settle && this.quietT >= o.quietNeed) { this.state = 'address'; this.overT = 0; this.vOver = 0; this.vh = [0, 0, 0]; this.tAddr = t; this.rKeep = rr; }
      break;
    case 'address': {
      const thr = this.thr(), vm = Math.hypot(this.vh[0], this.vh[1], this.vh[2]);
      this.overT = mag > thr ? this.overT + dt : 0;
      this.vOver = vm > Math.max(o.vTrig, 3.5 * this.noiseV) ? this.vOver + dt : 0;
      this.gOver = this.hasGyro && wmag > Math.max(o.gTrig, 5 * this.noiseW) ? this.gOver + dt : 0;
      // avec le gyro, la rotation décide du départ : la vitesse intégrée de l'accélération ne sert qu'en mode sans gyro (elle est trop sensible au recalage de la gravité juste après la stabilisation)
      if (this.overT >= o.trigger || (!this.hasGyro && this.vOver >= 0.05) || this.gOver >= 0.06) this._arm(i, thr);
      break;
    }
    case 'back': this._back(i, t); break;
    case 'fwd': this._fwd(i, t); break;
    case 'follow': this._follow(i, t, dt, Math.hypot(a[0], a[1], a[2])); break;
  }
  if (this.hasGyro && this.locked && (this.state === 'back' || this.state === 'fwd' || this.state === 'follow')) this._imperfAdvance(i);
  return this.state;
};

/* départ du geste : on remonte jusqu'au vrai début du mouvement */
P._arm = function (i, thr) {
  // origine de l'intégration de la vitesse : bien avant le déclenchement (au calme, l'accélération corrigée du biais est ≈ 0, intégrer ce calme ne coûte presque rien)
  // → un recul lent, détecté tard, n'est pas tronqué. Le vrai début est retrouvé à la fin du coup.
  let iv = i; const limV = Math.max(this.tAddr, this.T[i] - 3.0); while (iv > 0 && this.T[iv - 1] >= limV) iv--;
  let i0 = i; const lim = this.T[i] - 1.0, lvl = Math.max(0.04, 2 * this.noise);        // début estimé pour l'affichage en direct
  const lvlW = Math.max(0.012, 2 * this.noiseW);
  while (i0 > iv && (this.M[i0 - 1] > lvl || (this.hasGyro && this.Wm[i0 - 1] > lvlW)) && this.T[i0 - 1] > lim) i0--;
  this.iV0 = iv; this.i0 = iv; this.t0 = this.T[i0]; this.thr0 = thr;
  this.state = 'back'; this.locked = false; this.reached = false; this.vmin = 0;
  this.lockAt = this.t0 + this.o.lockDelay; this.f = null; this.note = '';
  this._axis(i);
};

/* axe du coup : sens moyen de la première poussée = recul ; l'avant est l'opposé */
P._axis = function (i) {
  const m = [0, 0, 0];
  for (let j = this.i0 + 1; j <= i; j++) { const d = this.T[j] - this.T[j - 1]; m[0] += this.A[j][0] * d; m[1] += this.A[j][1] * d; m[2] += this.A[j][2] * d; }
  const len = Math.hypot(m[0], m[1], m[2]);
  this.vLen = len;                                          // vitesse intégrée depuis le départ (m/s)
  if (this.hasGyro) {                                       // axe de rotation du coup = sens de la rotation du recul (gyro : très sensible, sans dérive)
    const th = [0, 0, 0]; for (let j = this.i0 + 1; j <= i; j++) { const d = this.T[j] - this.T[j - 1]; th[0] += this.W[j][0] * d; th[1] += this.W[j][1] * d; th[2] += this.W[j][2] * d; }
    const al = Math.hypot(th[0], th[1], th[2]); this.angLen = al; this.nHat = al > 1e-9 ? [th[0] / al, th[1] / al, th[2] / al] : [0, 1, 0];
  }
  this.f = len > 1e-9 ? [-m[0] / len, -m[1] / len, -m[2] / len] : [-1, 0, 0];
  this._recomputeV(i);
};
P._vNext = function (i, t) {                                // vitesse (avant > 0) : gyro (v = −L·ω·n) ou accélération intégrée
  return this.hasGyro ? -this.lever * dot(this.W[i], this.nHat) : this.V[i - 1] + dot(this.A[i], this.f) * (t - this.T[i - 1]);
};
P._recomputeV = function (i) {
  if (this.hasGyro) { for (let j = this.i0; j <= i; j++) this.V[j] = -this.lever * dot(this.W[j], this.nHat); return; }
  this.V[this.i0] = 0;
  for (let j = this.i0 + 1; j <= i; j++) this.V[j] = this.V[j - 1] + dot(this.A[j], this.f) * (this.T[j] - this.T[j - 1]);
};

P._abort = function (why) {
  this.aborts++; this.note = why; this.state = 'settle'; this.tReset = this.tPrev; this.quietT = 0; this.overT = 0;
  this.t0 = this.tTop = this.tImp = this.tEnd = null; this.i0 = this.iTop = this.iImp = this.iEnd = -1; this.f = null; this.locked = false; this.AL = this.YW = this.nRef = null;
};

P._back = function (i, t) {
  const o = this.o;
  if (!this.locked) {
    this._axis(i);
    if (t >= this.lockAt && (this.hasGyro ? this.angLen >= o.lockAng : this.vLen >= o.lockV)) this.locked = true;
    else if (t - this.t0 > o.lockMax) return this._abort('mouvement trop faible');
  } else this.V[i] = this._vNext(i, t);
  const v = this.V[i];
  if (v < this.vmin) this.vmin = v;
  if (v < -o.minBackV) this.reached = true;
  if (t - this.t0 > o.maxBack) return this._abort('backswing trop long');
  if (!this.reached) { if (t - this.t0 > 2.0) this._abort('pas de recul franc'); return; }
  if (v >= 0.3 * this.vmin + 0.01) {                       // la vitesse de recul est retombée (à la dérive près) : sommet ; précisé à la fin du coup
    this.tTop = t; this.iTop = i; this.state = 'fwd'; this.vmax = v; this.tVmax = t;
  }
};

P._fwd = function (i, t) {
  const o = this.o;
  this.V[i] = this._vNext(i, t);
  const v = this.V[i];
  if (v > this.vmax) { this.vmax = v; this.tVmax = t; }
  if (t - this.tTop > o.maxFwd) return this._abort('forward swing trop long');
  if (this.vmax < o.minVmax) { if (t - this.tTop > 1.2) this._abort('forward swing trop faible'); return; }
  if (t - this.tVmax >= 0.05 && t - this.tTop >= 0.1 && v < 0.985 * this.vmax) this._impact(i);
};

/* impact : le pic de vitesse avant, ou le choc le plus net (saut d'accélération brute) dans ±80 ms autour */
P._impact = function (i) {
  const T = this.T, R = this.R, b = this.bias, f = this.f;
  const raw = j => (R[0][j] - b[0]) * f[0] + (R[1][j] - b[1]) * f[1] + (R[2][j] - b[2]) * f[2];
  let lo = i; while (lo > this.iTop + 1 && T[lo - 1] >= this.tVmax - 0.08) lo--;
  const d = []; for (let j = this.iTop + 1; j <= i; j++) d.push([j, Math.abs(raw(j) - raw(j - 1))]);
  const base = d.filter(e => e[0] < lo).map(e => e[1]).sort((p, q) => p - q);
  const med = base.length >= 5 ? base[base.length >> 1] : 0.5;
  let pk = 0, ip = -1; for (const e of d) if (e[0] >= lo && e[1] > pk) { pk = e[1]; ip = e[0]; }
  if (ip >= 0 && pk > Math.max(3, 4 * med)) { this.shock = true; this.iImp = ip; this.tImp = T[ip]; }
  else { this.shock = false; this.tImp = this.tVmax; let j = i; while (j > this.iTop && T[j] > this.tImp) j--; this.iImp = j; }
  this.state = 'follow'; this.quietT = 0;
};

P._follow = function (i, t, dt, mag) {
  const o = this.o;
  this.V[i] = this._vNext(i, t);
  this.quietT = mag < Math.max(0.5 * this.thr0, 2.5 * this.noise, 0.06) ? this.quietT + dt : 0;
  if (this.quietT >= o.endQuiet) this._finish(i, t - o.endQuiet);
  else if (t - this.tImp > o.maxFollow) this._finish(i, t);
};

P._finish = function (i, tEnd) {
  let j = i; while (j > this.iImp && this.T[j] > tEnd) j--;
  this.tEnd = tEnd; this.iEnd = j; this._fitLever(); this._refineOnset(); this._refineTop(); this._refineImpact();
  const m = this._metrics();                                // un vrai putt : recul d'au moins 3 cm, impact à plus de 8 cm/s, durées plausibles (écarte balancement du corps, tremblement, geste parasite)
  if (m.lenBack < 0.03 || m.vImpact < 0.08 || m.back < 0.2 || m.fwd < 0.08) { this._abort('geste trop petit'); return; }
  this.state = 'done'; this.metrics = m;
};

/* bras de levier L (v = L·ω) : on compare la vitesse du téléphone issue de l'accélération (dérive retirée, arrêt final) à la vitesse angulaire.
   Les deux mesurent le même mouvement ; l'accélération donne l'échelle, le gyro la forme sans dérive. */
P._fitLever = function () {
  if (!this.hasGyro || !this.f) return;
  const T = this.T, i0 = this.i0, iE = this.iEnd, W = this.W, nH = this.nHat; let va = 0; const Va = [0];
  for (let j = i0 + 1; j <= iE; j++) { va += dot(this.A[j], this.f) * (T[j] - T[j - 1]); Va.push(va); }
  const span = T[iE] - T[i0] || 1, vEnd = va; let num = 0, den = 0;
  for (let j = i0; j <= iE; j++) { const vc = Va[j - i0] - vEnd * (T[j] - T[i0]) / span, wf = -dot(W[j], nH); num += vc * wf; den += wf * wf; }
  let vmax = 0; for (let j = i0; j <= iE; j++) vmax = Math.max(vmax, Math.abs(-dot(W[j], nH)) * this.lever);
  const L = den > 1e-4 ? num / den : 0;
  // seulement si le geste est assez vif : sinon le rapport accélération/gyro est trop bruité et on garde le L déjà appris
  if (vmax >= 0.25 && L > 0.4 && L < 3) { this.leverFit = L; this.lever = 0.5 * this.lever + 0.5 * L; for (let j = i0; j < this.V.length; j++) this.V[j] = -L * dot(W[j], nH); }
};

/* vrai début du geste : en remontant depuis le creux de vitesse (milieu du recul), dernier instant où la vitesse est encore ≈ 0 */
P._refineOnset = function () {
  const T = this.T, V = this.V; let km = this.i0, vmin = 0;
  for (let j = this.i0; j <= this.iTop; j++) if (V[j] < vmin) { vmin = V[j]; km = j; }
  const lim = 0.08 * Math.abs(vmin) + 0.003; let j = km; while (j > this.i0 && Math.abs(V[j]) > lim) j--;
  if (j <= this.i0) { j = Math.max(this.i0, this.T.findIndex(t => t >= this.t0)); }          // introuvable : on garde l'estimation du départ
  if (!this.hasGyro) { const base = V[j]; for (let k = j; k < V.length; k++) V[k] -= base; }      // vitesse intégrée : on recale l'origine ; en mode gyro elle est absolue (−L·ω), rien à décaler
  this.i0 = j; this.t0 = T[j];
};

/* ── imperfections horizontales du geste (mode gyro) ──
   Le gyro donne la rotation du putter ω. Avec « le haut » u (gravité suivie) :
   - rotation autour de la verticale (ω·u) intégrée → angle de la FACE par rapport à l'adresse (ψ, > 0 = vers la droite de la ligne) ;
   - la partie horizontale de ω est la normale du plan de swing ; son azimut, comparé à celui du recul, donne l'angle de la TRAJECTOIRE de la tête (φ, > 0 = vers la droite).
   La ligne de référence est celle du recul : on suppose qu'il suit la ligne de visée et que la face est perpendiculaire à l'adresse (un défaut de visée ne se voit pas). */
P._imperfAdvance = function (i) {
  const T = this.T, W = this.W, U = this.U, i0 = this.i0;
  if (!this.AL) {                                            // première fois (axe fixé) : référence = plan du recul
    const uR = [0, 0, 0]; for (let j = i0; j <= i; j++) { uR[0] += U[j][0]; uR[1] += U[j][1]; uR[2] += U[j][2]; }
    const nu = Math.hypot(uR[0], uR[1], uR[2]) || 1; uR[0] /= nu; uR[1] /= nu; uR[2] /= nu;
    const d = dot(this.nHat, uR), n = [this.nHat[0] - d * uR[0], this.nHat[1] - d * uR[1], this.nHat[2] - d * uR[2]], nn = Math.hypot(n[0], n[1], n[2]) || 1;
    this.nRef = [n[0] / nn, n[1] / nn, n[2] / nn]; this.AL = []; this.YW = []; this.iAz = i0; this.AL[i0] = 0; this.YW[i0] = 0;
  }
  for (let j = Math.max(this.iAz + 1, i0 + 1); j <= i; j++) {
    const dt = T[j] - T[j - 1], u = U[j], w = W[j], wv = dot(w, u), wh = [w[0] - wv * u[0], w[1] - wv * u[1], w[2] - wv * u[2]], mh = Math.hypot(wh[0], wh[1], wh[2]);
    let al = this.AL[j - 1];
    if (mh > 0.12) {                                         // assez de rotation pour que la direction du plan soit fiable
      const s = dot(wh, this.nRef) >= 0 ? 1 / mh : -1 / mh, nt = [wh[0] * s, wh[1] * s, wh[2] * s];
      const dr = dot(this.nRef, u), nr = [this.nRef[0] - dr * u[0], this.nRef[1] - dr * u[1], this.nRef[2] - dr * u[2]], nl = Math.hypot(nr[0], nr[1], nr[2]) || 1;
      const nR = [nr[0] / nl, nr[1] / nl, nr[2] / nl], cr = [nR[1] * nt[2] - nR[2] * nt[1], nR[2] * nt[0] - nR[0] * nt[2], nR[0] * nt[1] - nR[1] * nt[0]];
      const raw = Math.atan2(dot(cr, u), dot(nR, nt)); al += (raw - al) * (1 - Math.exp(-dt / 0.05));
    }
    this.AL[j] = al; this.YW[j] = this.YW[j - 1] - wv * dt;     // YW : angle de la face (cumul), + = vers la droite
  }
  this.iAz = i;
};

/* sommet précis : la vitesse sans dérive (nulle à l'arrêt final) repasse par zéro, au plus près du sommet détecté en direct */
P._refineTop = function () {
  const T = this.T, V = this.V, i0 = this.i0, iE = this.iEnd, span = T[iE] - T[i0] || 1, vEnd = V[iE];
  const vc = j => V[j] - vEnd * (T[j] - T[i0]) / span;
  let lo = this.iTop, hi = this.iTop; while (lo > i0 + 1 && T[lo] > this.tTop - 0.5) lo--; while (hi < this.iImp - 1 && T[hi] < this.tTop + 0.5) hi++;
  let best = -1, bd = 1e9;
  for (let j = lo; j < hi; j++) if (vc(j) < 0 && vc(j + 1) >= 0) { const d = Math.abs(T[j] - this.tTop); if (d < bd) { bd = d; best = j; } }
  if (best >= 0) { const a = vc(best), b = vc(best + 1), u = b - a > 0 ? -a / (b - a) : 0; this.tTop = T[best] + u * (T[best + 1] - T[best]); this.iTop = best + 1; }
};

/* impact précis : la tête revient à l'endroit de l'adresse (où est la balle), donc l'avance depuis le sommet égale la longueur du recul.
   Le pic de vitesse ne convient pas quand la main décélère avant l'impact (fréquent) : il tomberait trop tôt. */
P._refineImpact = function () {
  const T = this.T, V = this.V, i0 = this.i0, iE = this.iEnd, iT = this.iTop;
  const span = T[iE] - T[i0] || 1, vEnd = V[iE], vc = j => V[j] - vEnd * (T[j] - T[i0]) / span;
  let Lb = 0; for (let j = i0 + 1; j <= iT; j++) Lb -= vc(j) * (T[j] - T[j - 1]);
  if (Lb < 0.03) return;
  let d = 0, jg = -1, tg = 0;
  for (let j = iT + 1; j <= iE; j++) { const dd = vc(j) * (T[j] - T[j - 1]); if (d + dd >= Lb) { jg = j; tg = T[j - 1] + (dd > 0 ? (Lb - d) / dd : 0) * (T[j] - T[j - 1]); break; } d += dd; }
  if (jg < 0) return;                                        // l'avance n'atteint pas la longueur du recul : on garde l'impact détecté en direct
  if (this.shock && Math.abs(this.tImp - tg) < 0.04) return; // un choc net, cohérent avec la géométrie, est plus précis
  if (tg >= this.tVmax - 0.1) { this.tImp = tg; this.iImp = jg; this.shock = false; }       // (jamais bien avant le pic de vitesse : ce serait une erreur de mesure)
};

/* mesures du coup ; la dérive de l'intégration est retirée en forçant la vitesse à 0 à la fin (main immobile) */
P._metrics = function () {
  const T = this.T, V = this.V, i0 = this.i0, iE = this.iEnd, span = T[iE] - T[i0] || 1, vEnd = V[iE];
  const vc = j => V[j] - vEnd * (T[j] - T[i0]) / span;
  let aBack = 0, aFwd = 0, lenBack = 0, lenFwd = 0;
  for (let j = i0; j <= this.iTop; j++) { aBack = Math.max(aBack, -dot(this.A[j], this.f)); if (j > i0) lenBack -= vc(j) * (T[j] - T[j - 1]); }
  for (let j = this.iTop; j <= this.iImp; j++) { aFwd = Math.max(aFwd, dot(this.A[j], this.f)); if (j > this.iTop) lenFwd += vc(j) * (T[j] - T[j - 1]); }
  let face = 0, path = 0, lat = 0;
  if (this.AL) {
    const y0 = this.YW[this.AL[i0] !== undefined ? i0 : this.iAz] || 0, jI = Math.min(this.iImp, this.iAz);
    face = (this.YW[jI] - y0) * 180 / Math.PI; path = -this.AL[jI] * 180 / Math.PI;
    for (let j = Math.max(i0 + 1, this.iTop + 1); j <= jI; j++) lat += vc(j) * Math.sin(-this.AL[j]) * (T[j] - T[j - 1]);
    lat *= 1000;
  }
  const back = this.tTop - this.t0, fwd = this.tImp - this.tTop;
  return { back, fwd, follow: this.tEnd - this.tImp, tempo: fwd > 0 ? back / fwd : null, aBack, aFwd, vImpact: vc(this.iImp), lenBack, lenFwd, shock: this.shock, face, path, lateral: lat };
};

/* accélération signée (brute, biais retiré) de l'échantillon j sur l'axe du coup ; norme tant que l'axe n'existe pas */
P.signed = function (j) {
  const b = this.bias, R = this.R, x = R[0][j] - b[0], y = R[1][j] - b[1], z = R[2][j] - b[2];
  return this.f ? x * this.f[0] + y * this.f[1] + z * this.f[2] : Math.hypot(x, y, z);
};

if (typeof module !== 'undefined' && module.exports) module.exports = StrokeDetector; else root.StrokeDetector = StrokeDetector;
})(typeof self !== 'undefined' ? self : this);
