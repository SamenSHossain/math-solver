# Conventions and formula audit: Kerr–Newman Einstein–Maxwell in Lean/Mathlib

I audited the platform definitions independently, using
`/root/prove2me_workspace/Definitions/Def_NoHair_coordinates.lean` (this file holds all the Kerr–Newman definitions as well as the geometry), `Def_NoHair_kerrNewman.lean` and `Def_NoHair_spacetime.lean`, together with the proof files under `/home/user/math-solver/prove2me/nohair/`.

All scripts and their outputs are in this directory and can be rerun with `python3 <script>`:

| script | what it checks | method |
|---|---|---|
| `audit_conv.py` → `audit_conv.out` | A: curvature conventions (S², S³, H²); Reissner–Nordström with the platform formulas; D8: Gröbner basis | SymPy, exact |
| `audit_sym.py` → `audit_sym.out` | D1–D3: ∂r, atoms, relations, the Lean closed forms `dRt dKt dWt dfA dHA`, nullity, geodesy | SymPy, exact (pseudo-remainder modulo the quartic) |
| `audit_sym2.py` → `audit_sym2.out` | D4–D7: alignment and λ, flat Maxwell, ψ, Appell, inverse metric, Christoffel trace | SymPy, exact (rational parametrisation of the variety) |
| `audit_d5.py` → `audit_d5.out` | D2/D5: generic linear algebra (det, inverse, raising lemma) | SymPy, exact |
| `audit_extra.py` → `audit_extra.out` | compact ∂ⱼkₗ, expansion and twist, limits at the disc | SymPy, exact |
| `audit_bl.py` → `audit_bl.out` | B: Kerr–Schild → Boyer–Lindquist; potential; frame dragging | SymPy, exact |
| `audit_region.py` → `audit_region.out` | C: zero set of `ksRadius`; jump of k₃ at the disc; closed-timelike-curve remark | mpmath at 50 digits, 20 000 random points |
| `audit_num.py` → `audit_num.out` | the whole `EinsteinMaxwellAt` (Einstein, curved Maxwell, Bianchi), det g, R, Christoffel trace, at 10 points and parameter sets | mpmath at 60 digits; numerical differentiation `mp.diff` of the definitions as written |
| `audit_closed.py` → `audit_closed.out` | the Lean closed forms `Gam` (40 components) and `RicA` (10 components) against independent numerics | mpmath at 60 digits |

How the two kinds of check work:

* **Exact zero test ("symbolic").** I treat x, y, z, r as independent variables, with r tied to the others by the quartic C := r⁴ − (ρ² − a²) r² − a² z² = 0, where ρ² = x² + y² + z².
  * Derivatives use the chain rule with ∂ᵢr = −∂ᵢC / ∂ᵣC (implicit function theorem).
  * An expression is shown to vanish on {C = 0, r > 0} in one of two ways: either the pseudo-remainder of its numerator modulo C (which is monic in r) is 0, or its pull-back under the parametrisation (r, k⃗) ↦ (x, y, z) = (r k₁ − a k₂, a k₁ + r k₂, r k₃) is identically 0. In the second case k⃗ is a rational parametrisation of S². This map is a bijection from (0, ∞) × S² onto ℝ³ minus the disc (see C).
  * None of these checks uses the repo's generators.
* **Numerical check.** The definitions are transcribed literally: `ksRadius` is the nested-square-root formula, `invMetric` is a matrix inverse, `riemann` uses exactly the index pattern of the Lean code, and so on. Every first and second partial derivative is computed by `mpmath.diff` at 60 digits. Residuals are around 1e-56 to 1e-62, against field and curvature scales of order 1e-2 to 10.

---

## A. Conventions

**Signature and coordinates.** The coordinates are y = (y⁰, y¹, y², y³) = (t, x, y, z) with η = diag(−1, 1, 1, 1), so the signature is (−, +, +, +).

**Christoffel symbols** (`christoffel G y i j k`). This is the standard Levi-Civita formula, symmetric in j and k:
$$\Gamma^i{}_{jk}=\tfrac12 g^{il}\big(\partial_j g_{lk}+\partial_k g_{lj}-\partial_l g_{jk}\big).$$

**Riemann tensor** (`riemann G y ρ σ μ ν`):
$$R^\rho{}_{\sigma\mu\nu}=\partial_\mu\Gamma^\rho{}_{\nu\sigma}-\partial_\nu\Gamma^\rho{}_{\mu\sigma}+\Gamma^\rho{}_{\mu\lambda}\Gamma^\lambda{}_{\nu\sigma}-\Gamma^\rho{}_{\nu\lambda}\Gamma^\lambda{}_{\mu\sigma}.$$
* This is literally Carroll's eq. (3.113) and the MTW convention. In MTW's sign classification it is "+ + +": metric signature −+++, Riemann sign +, Einstein equation G = +8πT.
* Wald writes the Riemann tensor with different index placement, R_{abc}{}^d with (∇_a∇_b − ∇_b∇_a)ω_c = R_{abc}{}^d ω_d. The translation is R^ρ_{σμν}(MTW) = −R_{μνσ}{}^ρ(Wald). His Ricci tensor R_{ac} = R_{abc}{}^b nevertheless coincides with the one here, so Ricci, R and G all agree with Wald.

**Ricci, scalar and Einstein tensors.**
$$R_{\sigma\nu}=R^\rho{}_{\sigma\rho\nu},\qquad R=g^{\sigma\nu}R_{\sigma\nu},\qquad G_{\mu\nu}=R_{\mu\nu}-\tfrac12Rg_{\mu\nu}.$$
The Ricci tensor contracts the first index with the third.

**Sign check (exact, `audit_conv.py`).** I ran the Lean formulas, transcribed literally and generic in dimension, on known spaces:

| space | result |
|---|---|
| 2-sphere of radius R | R^θ_{φθφ} = sin²θ, Ric = diag(1, sin²θ), scalar curvature 2/R² > 0 |
| unit 3-sphere | scalar curvature 6 |
| hyperbolic plane | scalar curvature −2 |

So round spheres have positive curvature: this is the standard sign.

**Maxwell source** (`maxwellSource`):
$$2\Big(\sum_{\alpha\beta}F_{\mu\alpha}g^{\alpha\beta}F_{\nu\beta}-\tfrac14 g_{\mu\nu}F_{\alpha\beta}F^{\alpha\beta}\Big)=2\big(F_{\mu\alpha}F_\nu{}^\alpha-\tfrac14g_{\mu\nu}F^2\big)=8\pi T_{\mu\nu},$$
$$T_{\mu\nu}=\frac1{4\pi}\Big(F_{\mu\alpha}F_\nu{}^\alpha-\tfrac14 g_{\mu\nu}F_{\alpha\beta}F^{\alpha\beta}\Big).$$
* Here F_ν{}^α = g^{αβ} F_{νβ}, which is exactly the platform's contraction Σ F_{μα} g^{αβ} F_{νβ}. The expression is symmetric in μ and ν.
* These are Gaussian units with G = c = 1 ("geometrized Gaussian").
* In flat space this gives T₀₀ = (E² + B²)/8π > 0.

**Normalization cross-check (exact).** I took Reissner–Nordström in Schwarzschild coordinates, with −g_tt = 1 − 2M/r + Q²/r² and A = −(Q/r) dt, and fed it through the platform formulas literally. The result is `einsteinTensor = maxwellSource` exactly, and R = 0. This confirms two things:
* The metric carries +Q²/r² (not Q²/4π) together with the factor 2 in the source.
* The energy density is positive: T_tt/(−g_tt) = Q²/(8π r⁴).

**Maxwell equations.** The second clause, ∂_μ(√|det g| F^{μν}) = 0, is equivalent to ∇_μF^{μν} = 0 (source-free). The third clause is dF = 0, written cyclically.

**Lean-specific points the paper may mention.**
* `coordPartial f k y = fderiv ℝ f y (e_k)`. At points where r > 0 everything is real-analytic, so this is the classical partial derivative.
* `invMetric` is Mathlib's matrix inverse, which returns a junk value for singular matrices. That never happens here, since det g = −1 on U.
* `fderiv` is 0 at points where the function is not differentiable. The proof uses this deliberately in `cp_time` (see E).

---

## B. Kerr–Newman in Kerr–Schild form

**Platform definitions (verbatim):**
$$g_{\mu\nu}=\eta_{\mu\nu}+f\,k_\mu k_\nu,\qquad k_\mu=\Big(1,\ \frac{rx+ay}{r^2+a^2},\ \frac{ry-ax}{r^2+a^2},\ \frac zr\Big),$$
$$f=\frac{r^2(2mr-e^2)}{r^4+a^2z^2},\qquad A_\mu=\frac{e\,r^3}{r^4+a^2z^2}\,k_\mu,\qquad F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu ,$$
$$r=\sqrt{\tfrac12\big(\rho^2-a^2+\sqrt{(\rho^2-a^2)^2+4a^2z^2}\big)},\qquad \rho^2=x^2+y^2+z^2 .$$
* k is a covector with lower index and k₀ = +1.
* `ksRadius` is the explicit non-negative root. When r > 0 it is equivalent to the spheroid equation (x² + y²)/(r² + a²) + z²/r² = 1. When r = 0 that equation is meaningless (see C).

**Exact identification with Boyer–Lindquist Kerr–Newman (`audit_bl.py`).**
1. Use the spheroidal parametrisation x + iy = (r + ia) sinθ e^{iφ}, z = r cosθ. Then:
   * (x² + y²)/(r² + a²) + z²/r² = 1.
   * The spatial part of k is the unit vector k⃗ = (sinθ cosφ, sinθ sinφ, cosθ).
   * The pulled-back covector is
     $$k=dt+dr-a\sin^2\theta\,d\phi .$$
   * With Σ = r² + a² cos²θ, f = (2mr − e²)/Σ and H = e r/Σ.
2. Change coordinates by t = t_BL + ∫((r² + a²)/Δ − 1) dr and φ = φ_BL + ∫ a/Δ dr, with Δ = r² − 2mr + a² + e². The metric becomes **exactly** the standard Boyer–Lindquist Kerr–Newman metric:
$$ds^2=-\Big(1-\tfrac{2mr-e^2}{\Sigma}\Big)dt^2-\tfrac{2a\sin^2\theta(2mr-e^2)}{\Sigma}\,dt\,d\phi+\tfrac{\Sigma}{\Delta}dr^2+\Sigma d\theta^2+\Big(r^2+a^2+\tfrac{a^2\sin^2\theta(2mr-e^2)}{\Sigma}\Big)\sin^2\theta\,d\phi^2 .$$
3. The potential becomes
   $$A=\frac{er}{\Sigma}(dt-a\sin^2\theta\,d\phi)+\frac{er}{\Delta}dr .$$
   The last term depends only on r, so it is exact. Hence A ≃ (e r/Σ)(dt − a sin²θ dφ).

**Literature.** I could not reach Wikipedia or arXiv from this sandbox (the proxy returned 403), so the following is from memory, and the paper must check the cited equation numbers. The platform's form is the standard Kerr–Schild Cartesian form, with the same k, f ∝ 2Mr − Q² and A = Q r³/(r⁴ + a²z²) k, as in:
* Kerr 1963;
* Debney–Kerr–Schild 1969 (J. Math. Phys. 10, 1842);
* Visser, arXiv:0706.0622, Kerr–Schild "Cartesian" section (Kerr only: f = 2mr³/(r⁴ + a²z²));
* Wikipedia, "Kerr–Newman metric", Kerr–Schild section.

The identification above is self-contained and is what should be relied on.

**Sign-convention subtleties the paper should state.**

1. **The chart is ingoing (time orientation).** With ∂_t future-directed at infinity, the congruence −k^♯ = (1, −k⃗) is future-directed and ingoing.
   * For a = e = 0 the metric is g = η + (2m/r)(dt + dr)². This is ingoing Eddington–Finkelstein with t = v − r.
   * The chart is regular across the **future** horizon(s). It should be called "ingoing Kerr–Schild" coordinates.
2. **Sense of rotation.** J = +ma ẑ. Two independent signs agree:
   * frame dragging ω = −g_tφ/g_φφ ≈ 2ma/r³;
   * the gauge-invariant part of g₀ᵢ, which is (2ma/r³)(y, −x, 0) and has the Lense–Thirring form for J = ma ẑ.

   Replacing a by −a is equivalent to the reflection y ↦ −y. Some sources use the opposite orientation. This does not matter for the theorem, since a ∈ ℝ is arbitrary.
3. **Sign of the charge (a discrepancy of naming, not of mathematics).** With ∂_t future-directed and the usual (−+++) conventions (A_μ = (−φ, A⃗), E_i = F_{i0}, F_{ij} = ε_{ijk}B_k):
   * E = ∇H ≈ −e x⃗/r³.
   * So the physical (MTW) charge is **Q = −e**. MTW's A = −(Q r/Σ)(dt − a sin²θ dφ) matches the platform's A with Q = −e.
   * Consistency check: the magnetic dipole moment is μ = −e a ẑ = Q a ẑ and J = m a ẑ, which gives gyromagnetic ratio g = 2, as it should.
   * Under time reversal (−∂_t future) the chart becomes outgoing (white-hole horizon regular), with Q = +e and J = −ma ẑ.
   * This is harmless. The metric depends only on e², F is linear in e, and the Einstein–Maxwell system is invariant under F ↦ −F. The platform's own `IsKerrNewmanDOC` also allows a duality rotation, with β = π giving −F.
   * Recommended wording: "charge parameter e (the physical charge is ±e depending on time orientation; |Q| = |e|)", or simply call e the charge "up to sign convention".
4. **Normalization of e versus Q.** These are Gaussian geometrized units, Δ = r² − 2mr + a² + e², so e is the charge in units with Coulomb force Q₁Q₂/r².
   * In SI units, e² ↔ G Q²/(4πε₀ c⁴).
   * In Heaviside–Lorentz (rationalized) units one would have T = FF − ¼ gF² and Q²/4π in Δ.

   Consistency is confirmed in three ways: by the theorem itself (the minus sign of e² in f), by the Reissner–Nordström check in A, and by the numerical checks.

---

## C. The region r > 0

**Zero set, read off the definition.** Let P = ρ² − a² and q = ½(P + √(P² + 4a²z²)), so that r = √q (`Real.sqrt`, which returns 0 for negative arguments).
* Since √(P² + 4a²z²) ≥ |P| ≥ −P, we always have q ≥ 0. So the junk branch of `Real.sqrt` is never used.
* q = 0 exactly when P ≤ 0 and a²z² = 0.

Therefore
$$\{r=0\}=\begin{cases}\mathbb R_t\times\bar D_a,\ \ \bar D_a=\{z=0,\ x^2+y^2\le a^2\} & a\ne0,\\ \mathbb R_t\times\{0\}\ \ (\text{a worldline}) & a=0,\end{cases}\qquad U=\{r>0\}=\mathbb R^4\setminus\{r=0\}\ \text{open}.$$

**Sampling check.** I tested 20 000 random points (`audit_region.py`), including a = 0, z = 0 and the origin.
* The characterisation above had **0 mismatches**.
* On U the quartic and the spheroid equation hold to 1e-40.
* ksRadius(−a) = ksRadius(a): `ksRadius` uses only `a ^ 2`, so r and U depend on a only through a². By contrast k, g and A do depend on the sign of a.
* When a = 0, r = |x⃗|.

**Geometry.**
* On U, r is real-analytic. The discriminant (ρ² − a²)² + 4a²z² is positive there; this is the Lean lemma `ks_D_pos`.
* The ring singularity is the rim {z = 0, x² + y² = a²}.
* The open disc is a branch cut: r → 0 continuously, but k₃ = z/r jumps from +√(1 − (x² + y²)/a²) to −√(1 − (x² + y²)/a²).
  * Numerically, at (0.3, −0.4, ±1e-9) with a = 0.8: k₃ = ±0.7806247498.
  * Exactly, f → −e²/(a² − x² − y²) as the disc is approached (`audit_extra.py`).
* Consequences for the excision:
  * If e ≠ 0, the metric components g₀₃ = f k₃ and the others are **discontinuous** across the open disc.
  * If e = 0, g is continuous there but not C¹: the disc carries a distributional source (Israel 1970).
  * So removing the closed disc is necessary, not an artefact of the formalisation.
* The theorem covers only the r > 0 sheet of the maximal analytic extension.
* The Appell square root (D6) has its principal-branch cut exactly on the closed disc.

**Parameters.** The theorem has no hypothesis on (m, a, e); `IsKerrNewmanBlackHoleParams` is *not* assumed. So "every point of U" includes:
* the exterior and the ergoregion;
* the horizons r = r± themselves (the chart is regular there) and the region between them;
* the region inside the inner horizon, near the ring;
* naked singularities (a² + e² > m²), negative m, and either sign of a.

Numerically I checked all of these (10 cases, D below).

**New subtlety: closed timelike curves inside U.** If a ≠ 0 and either e ≠ 0 or m < 0, the region U contains closed timelike curves.
* In Boyer–Lindquist form, g_φφ at θ = π/2 equals (r⁴ + a²r² + 2mra² − a²e²)/r², which is negative for small r > 0.
* Example: m = 1, a = 0.6, e = 0.5. On the circle t = const, z = 0, x² + y² = r² + a², the value of g_yy at (√(r² + a²), 0, 0) is −58.6 at r = 0.05, −3.86 at r = 0.1 and +4.375 at r = 0.2.
* For Kerr with m > 0 (e = 0) the closed timelike curves lie only on the r < 0 sheet, outside U.
* This does not affect the theorem, which is pointwise. But the paper must not describe U as causally well-behaved or globally hyperbolic.

**Special cases.**

| parameters | what the theorem gives |
|---|---|
| e = 0 | Kerr; F ≡ 0, so G_{μν} = R_{μν} = 0 (vacuum) |
| a = 0 | Reissner–Nordström in ingoing Kerr–Schild / Eddington–Finkelstein form (t = v − r): k = (1, x⃗/r), r = \|x⃗\|, f = 2m/r − e²/r², A = (e/r)(dt + dr) ≃ (e/r) dt; U = ℝ⁴ minus the worldline |
| a = e = 0 | Schwarzschild, g = η + (2m/r)(dt + dr)², ingoing Eddington–Finkelstein |
| m = a = 0 | g = η − (e²/r²) k⊗k: massless Reissner–Nordström (naked, repulsive), still an Einstein–Maxwell solution |
| m = e = 0 | g = η, F = 0: Minkowski minus a disc (or minus a worldline if a = 0) |

---

## D. Formulas to display (all verified)

### (1) The radius and the atoms (exact, `audit_sym.py`)

The quartic and the partial derivatives of r:
$$r^4-(\rho^2-a^2)r^2-a^2z^2=0,$$
$$\partial_x r=\frac{r^3x}{r^4+a^2z^2}=rW(rk_1-ak_2),\quad \partial_y r=\frac{r^3y}{r^4+a^2z^2}=rW(ak_1+rk_2),\quad \partial_z r=\frac{r(r^2+a^2)z}{r^4+a^2z^2}=(r^2+a^2)k_3W .$$

The atoms, and how they relate to x, y, z, f and H:
$$W=\frac1{r^2+a^2k_3^2}=\frac{r^2}{r^4+a^2z^2},\qquad x=rk_1-ak_2,\ \ y=ak_1+rk_2,\ \ z=rk_3\quad(x+iy=(r+ia)(k_1+ik_2)),$$
$$k_1^2+k_2^2+k_3^2=1\ \text{on }U,\qquad f=(2mr-e^2)W,\qquad H:=\frac{er^3}{r^4+a^2z^2}=erW .$$

A compact form of ∂ⱼkₗ that the paper can display:
$$\partial_jk_l=W\big[r(\delta_{jl}-k_jk_l)+a\,k_3\,\varepsilon_{ljm}k_m\big]\quad(j,l=1,2,3),\qquad \partial_0(\cdot)=0 .$$

All Lean atom closed forms match the independent implicit-differentiation derivatives exactly. That is 21 formulas: `dRt` (3), `dKt` (9 + zero row and column), `dWt` (3), `dfA` (3) and `dHA` (3).

### (2) Nullity, determinant and inverse (exact, generic f, `audit_d5.py`)

$$\eta^{\mu\nu}k_\mu k_\nu=-1+k_1^2+k_2^2+k_3^2=0,\qquad \det g=-1,\qquad g^{\mu\nu}=\eta^{\mu\nu}-f\,k^{\sharp\mu}k^{\sharp\nu},\quad k^\sharp=\eta k=(-1,k_1,k_2,k_3).$$
These follow from the matrix determinant lemma and the Sherman–Morrison formula, using kᵀη⁻¹k = 0.

### (3) The congruence is geodesic (exact)

$$k^{\sharp\nu}\partial_\nu k_\mu=\sum_i k_i\partial_ik_\mu=0,\qquad k^{\sharp\nu}\partial_\mu k_\nu=\tfrac12\partial_\mu(\eta^{\alpha\beta}k_\alpha k_\beta)=0 .$$
Also k⃗·∇r = 1 (r is an affine parameter) and k⃗·∇k⃗ = 0. So the spatial rays are straight lines: this is the Kerr congruence.

Expansion and twist (exact, `audit_extra.py`):
$$\nabla\!\cdot\vec k=2rW,\qquad \nabla\times\vec k=-2ak_3W\,\vec k .$$

### (4) Alignment (exact, `audit_sym2.py`)

$$F_{\mu\nu}k^{\sharp\nu}=\lambda k_\mu,\qquad \lambda=-k^{\sharp\nu}\partial_\nu H=-\vec k\cdot\nabla H=e\,(r^2-a^2k_3^2)\,W^2=\frac{e(r^2-a^2\cos^2\theta)}{\Sigma^2}.$$
* The sign matches `align_alg` in `Sol_NoHair_kerrNewman_maxwell.lean`: Σ_ν F_{μν} ks_ν = (−Σ_ν ∂_νH ks_ν) k_μ, with ks = k^♯.
* Mechanism: write F_{μν} = ∂_μH k_ν − ∂_νH k_μ + H(∂_μk_ν − ∂_νk_μ) and contract with k^♯. Nullity kills ∂_μH (k·k^♯) and H k^{♯ν}∂_μk_ν. Geodesy kills H k^{♯ν}∂_νk_μ.

### (5) Curved Maxwell reduces to flat Maxwell (exact, generic, `audit_d5.py`)

Suppose k is null, F is antisymmetric and F k^♯ = λ k. Then
$$(\eta-fk^\sharp k^{\sharp T})F(\eta-fk^\sharp k^{\sharp T})=\eta F\eta+f\lambda k^\sharp k^{\sharp T}-f\lambda k^\sharp k^{\sharp T}-f^2(k^{\sharp T}Fk^\sharp)k^\sharp k^{\sharp T}=\eta F\eta .$$
Since √|det g| = 1, this gives
$$\sqrt{|\det g|}\,F^{\mu\nu}=\eta^{\mu\alpha}\eta^{\nu\beta}F_{\alpha\beta}.$$
The constraint F k^♯ = λ k has rank 3; it determines F₀ᵢ, and F₁₂, F₁₃, F₂₃ remain free.

### (6) Flat Maxwell (exact, `audit_sym2.py`)

$$F_{i0}=\partial_iH\ (\vec E=\nabla H),\qquad F_{ij}=\varepsilon_{ijk}\partial_k\psi\ \ (\vec B=\nabla\times\vec A=\nabla\psi),\qquad \vec A=H\vec k,$$
$$\psi=\frac{e\,a\,z\,r}{r^4+a^2z^2}=e\,a\,k_3W,\qquad \Delta H=0,\quad \Delta\psi=0 .$$
* This ψ matches `psif`, and the identities match `iden_12/23/31`: F₁₂ = ∂_zψ, F₂₃ = ∂_xψ, F₃₁ = ∂_yψ.
* Flat Maxwell then follows:
  * ν = 0: ∂ᵢF^{i0} = −ΔH = 0;
  * ν = j: ∂ᵢF_{ij} = ε_{ijk}∂ᵢ∂ₖψ = 0.

**Appell potential (the clean statement).**
$$H+i\psi=\frac{e}{r-ia\cos\theta}=\frac{e}{r-iaz/r}=\frac{e}{\sqrt{x^2+y^2+(z-ia)^2}},\qquad \Big(r-\frac{iaz}{r}\Big)^2=x^2+y^2+(z-ia)^2\ \text{on }U,$$
$$\vec E+i\vec B=\nabla\Big(\frac{e}{\sqrt{x^2+y^2+(z-ia)^2}}\Big).$$
* The square root is the principal branch: its real part is r > 0. Its branch cut, {ρ² − a² − 2iaz ∈ (−∞, 0]}, is exactly the closed disc.
* So E + iB is the Coulomb field of a charge at the imaginary point (0, 0, ia) (Appell 1887; Newman; Lynden-Bell 2004).
* With the MTW orientation the charge is Q = −e (see B).
* The same complex combination equals the expansion and twist of the congruence:
  $$H+i\psi=e\big(\tfrac12\nabla\cdot\vec k-\tfrac i2\,\vec k\cdot\nabla\times\vec k\big)=e(r+iak_3)W .$$

### (7) Christoffel trace (exact for σ = 0, …, 3; numerically ~1e-61 at 10 points)

$$\sum_\rho\Gamma^\rho{}_{\rho\sigma}=\tfrac12g^{\rho l}\partial_\sigma g_{l\rho}=\tfrac12\partial_\sigma\log|\det g|=0\quad(\det g\equiv-1\ \text{on }U).$$

### (8) Gröbner basis (exact, `audit_conv.py`)

* Use lex order W > k₁ > r > k₂ > k₃ > a > m > e, with REL = k₁² + k₂² + k₃² − 1 and WREL = W(r² + a²k₃²) − 1.
* Their leading monomials are LM(REL) = k₁² and LM(WREL) = W r². These are coprime, so Buchberger's first criterion applies.
* `sympy.groebner` returns exactly {WREL, REL}, which is therefore the reduced Gröbner basis. The S-polynomial reduces to 0.

**Soundness.** Each Lean step is `linear_combination c₁*hrel + c₂*hW`. The tactic `ring` checks P − c₁·REL − c₂·WREL ≡ 0 as a polynomial identity. At the atoms of any point of U, REL = WREL = 0, so P = 0 there. No Gröbner-basis theory is trusted; the basis is only an offline tool for finding the cofactors.

**Completeness (remark, not needed for the proof).**
* The quotient ℚ[W, k, r, a, m, e]/⟨REL, WREL⟩ ≅ (ℚ[k, r, a, m, e]/⟨REL⟩)[1/(r² + a²k₃²)] is a domain, because REL is an irreducible quadric.
* The atom points of U are exactly (0, ∞) × S² × ℝ³, which is Zariski-dense.
* Hence the ideal is the full vanishing ideal: every true identity reduces to 0. This explains why division never fails.

### (9) Trace-free source and counting

* The 4D Maxwell stress is trace-free: g^{μν}T_{μν} = (1/4π)(F² − F²) = 0. So R = 0 and G_{μν} = R_{μν}.
  * Numerically |R| is between 1e-62 and 4e-57 at all 10 points.
  * In Lean this is `scal_zero`, a polynomial identity that needs only the `hrel` cofactor.
* Counting:
  * There are 4 × 10 = 40 independent Γ^i_{jk}. These are the Lean `G000 … G333` with j ≤ k: 40 definitions.
  * There are 30 divergence terms `DD` (ρ = 1, 2, 3 times 10). The ρ = 0 row of `dDivT` is identically 0.
  * There are 10 Ricci components `Ric00 … Ric33`; the others follow by symmetry.

### End-to-end numerical check of the whole statement (`audit_num.py`, 60 digits, verbatim definitions)

The table lists the largest residual in each equation:

| case | r | det g | max\|G−8πT\| (scale of T) | max\|∂(√\|g\|F^{μν})\| | dF | Σ Γ^ρ_ρσ |
|---|---|---|---|---|---|---|
| m = 1.1, a = 0.43, e = 0.4, exterior | 1.690 | −1 | 1e-61 (2e-2) | 9e-62 | 0 | 1e-61 |
| m = 1, a = 0.6, e = 0.5, inside r₋ | 0.297 | −1 | 3e-60 (3.3) | 1e-60 | 3e-61 | 3e-61 |
| same parameters, between the horizons | 1.185 | −1 | 8e-61 (0.16) | 2e-61 | 2e-62 | 2e-61 |
| m = 0.5, a = 1.2, e = 0.9 (naked) | 0.857 | −1 | 3e-61 (2.3) | 6e-61 | 0 | 6e-62 |
| m = −0.8, a = −0.7, e = 1.3 | 0.712 | −1 | 6e-60 (10.7) | 3e-60 | 0 | 5e-61 |
| m = 0.9, a = 0.8, e = 0.6, z = ±1e-3 above/below the disc | 0.00128 | −1 | 1e-56 (7.6) | 3e-59 | 6e-61 | 9e-61 |
| a = 0 (Reissner–Nordström) | 0.539 | −1 | 8e-60 (7.3) | 2e-60 | 0 | 2e-61 |
| m = a = 0, e = 0.7 | 1.241 | −1 | 2e-61 (0.27) | 8e-62 | 0 | 6e-62 |
| e = 0 (Kerr) | 1.928 | −1 | 2e-61 (Ricci-flat) | 0 | 0 | 6e-62 |

**Lean closed forms (`audit_closed.py`).** I parsed `Gam` (all 40 components) and `RicA` (10 components) from the Lean source and compared them with independent numerics at 3 parameter sets. The disagreement is at most 3e-60.

---

## E. What `Sol_NoHair_kerrNewman_einstein.lean` proves (plain mathematics)

Fix m, a, e and a point y with r(y) > 0. Let U = {r > 0}, which is open, and write 𝔞(w) = (r, k₁, k₂, k₃, W)(w) for the atoms. The proof uses two relations at every w ∈ U:
* `ks_rel`: k₁² + k₂² + k₃² = 1;
* `ks_W`: W(r² + a²k₃²) = 1.

**Imported platform theorems.** Each is proved separately, from the definition blocks.

| theorem | statement | how it is proved |
|---|---|---|
| `thm_christoffel` | for w ∈ U, Γ^i_{jk}(w) = Gam_{ijk}(𝔞(w)), where Gam is 40 explicit polynomials in the atoms (extended by j↔k symmetry) | `cp_metric` and `invMetric_eq`: g⁻¹ = η − f k^♯k^{♯T} |
| `thm_div_one/two/three` | for ρ = 1, 2, 3: w ↦ Gam_{ρνσ}(𝔞(w)) is differentiable at y, and ∂_ρ of it equals the polynomial dDivT_{ρνσ}(𝔞(y)) | the `HasCP` calculus |
| `thm_ricci_a/b/c` | RicS = RicA for the 10 components with μ ≤ ν, where RicS_{σν} = Σ_ρ dDivT_{ρνσ} − Σ_{ρ,l} Gam_{ρνl} Gam_{lρσ} | polynomial identities modulo the relations |
| `thm_maxwell` | FS = FA (F in closed form); g⁻¹FAg⁻¹ = FupA; FA:FupA = FFA; TS = RicA, where TS is maxwellSource in closed form | polynomial identities modulo the relations |

**Chain inside the file.**
1. `trGam`: Σ_ρ Gam_{ρρσ} = 0 modulo the relations (exact cofactors).
2. `cp_chr`: since U is open and Γ = Gam∘𝔞 on a neighbourhood of y, their coordinate partials agree at y (`EventuallyEq.fderiv_eq`).
3. `trace_cp_zero`: Σ_ρ ∂_νΓ^ρ_{ρσ}(y) = ∂_ν(Σ_ρ Γ^ρ_{ρσ})(y) = 0. This uses differentiability of each summand (`fderiv_fun_sum`) and the fact that the sum is identically 0 near y.
4. `cp_div`: ∂_ρΓ^ρ_{νσ}(y) = dDivT_{ρνσ}.
   * For ρ = 0 this follows from `cp_time`: for **any** Φ, w ↦ Φ(r(w), k₁(w), k₂(w), k₃(w)) is invariant under t-translation (r and k do not depend on y⁰), so its ∂₀ is 0.
   * If the function is differentiable, this is the derivative of a constant along the line. If it is not, Mathlib's `fderiv` is 0 by convention. Either way no differentiability hypothesis is needed.
   * For ρ = 1, 2, 3 it follows from `thm_div_*`.
5. `ricci_eq`: unfolding the Lean definitions gives
   $$R_{\sigma\nu}=\sum_\rho\partial_\rho\Gamma^\rho{}_{\nu\sigma}-\partial_\nu\Big(\sum_\rho\Gamma^\rho{}_{\rho\sigma}\Big)+\sum_{\rho,l}\big(\Gamma^\rho{}_{\rho l}\Gamma^l{}_{\nu\sigma}-\Gamma^\rho{}_{\nu l}\Gamma^l{}_{\rho\sigma}\big).$$
   The second term is 0 by step 3, and the first part of the third term is 0 by `trGam`. What remains is RicS(𝔞(y)), which equals RicA(𝔞(y)) by `thm_ricci_*`. The components with μ > ν follow from `RicS_symm` and `RicA_symm`.
6. `scal_eq`: R(y) = Σ (η − f k^♯k^{♯T})^{σν} RicA_{σν} = 0 (`scal_zero`, polynomial identity).
7. **`einstein_eq`**: G_{μν}(y) = R_{μν} − ½ R g_{μν} = RicA_{μν}(𝔞(y)).
8. Maxwell side:
   * `pot_eq`: e r³/(r⁴ + a²z²) = H(𝔞) = e r W.
   * `field_closed`: F_{μν}(y) = FA_{μν}(𝔞(y)), via HasCP for H·k_ν, `hasCP_H` and `hasCP_K`.
   * `metric_closed`: g = gA(𝔞).
   * `invMetric_eq`: g⁻¹ = ginvA(𝔞).
9. **`maxwell_eq`**: the platform contractions are rewritten in closed form. Then F^{αβ} = FupA, F_{αβ}F^{αβ} = FFA, and maxwellSource_{μν}(y) = TS_{μν}(𝔞(y)) = RicA_{μν}(𝔞(y)).
10. **`solution`**: einsteinTensor_{μν}(y) = RicA_{μν} = maxwellSource_{μν}(y).

Both `einstein_eq` and `maxwell_eq` therefore state "the platform quantity at y equals the same closed-form polynomial RicA_{μν} evaluated at the atoms of y". The top-level `NoHair.kerrNewman_einsteinMaxwell` is the conjunction of `kerrNewman_einstein`, `kerrNewman_maxwell` and `kerrNewman_field_closed`.

**Hygiene.** A grep shows that `sorry` appears only in the statement files `Thm_*.lean`, which are platform statement stubs by design. There is no `sorry`, `axiom` or `native_decide` in any `Sol_*` file or `Def_*` block. `EXPLANATION.md` reports the axioms as `propext`, `Classical.choice` and `Quot.sound`.

---

## Discrepancies and subtleties the paper must state

1. **Charge sign.** With ∂_t future-directed and MTW conventions (E_i = F_{i0}), the physical charge is Q = −e, so A matches MTW with Q = −e. As a check, μ = Q a ẑ, J = m a ẑ and g = 2. This is harmless because of the F ↦ −F symmetry and because e ranges over ℝ. Call e the "charge parameter".
2. **The chart is ingoing Kerr–Schild** (future horizon regular), and the rotation is J = +ma ẑ. The sign of a differs from some references; a ↦ −a is the same as y ↦ −y.
3. **Units.** Gaussian geometrized units: e² appears in f and Δ = r² − 2mr + a² + e², and 8πT = 2(FF − ¼ gF²).
4. **How r is defined.** `ksRadius` is the explicit non-negative root formula. It satisfies the spheroid equation only where r > 0. The `Real.sqrt` junk value is never triggered, since the argument is always ≥ 0.
5. **The excised set is ℝ_t × closed disc** (a ≠ 0), or the worldline x⃗ = 0 (a = 0), and depends on a only through a². Excising the open disc is necessary: for e ≠ 0 the metric is discontinuous across it, and for e = 0 it is only C⁰ there.
6. **U contains closed timelike curves** near the ring when a ≠ 0 and (e ≠ 0 or m < 0). The theorem is pointwise and unaffected, but U should not be called globally hyperbolic or causal.
7. **No parameter restriction.** The theorem holds for all real m, a, e, including the horizons themselves and naked singularities. The black-hole inequality is not used.
8. **Lean conventions.** The proof relies on the Mathlib convention that `fderiv` is 0 where a function is not differentiable (in `cp_time`), and on `invMetric` being a matrix inverse. Both are legitimate, and both are worth a sentence.
9. **Literature citations.** I could not check them online from this sandbox. The authors must verify the Visser, Wikipedia and Debney–Kerr–Schild equation numbers and their sign of a and of the charge. The internal identification with Boyer–Lindquist (B) is exact and self-contained.
10. **The computed task's claims are confirmed.** No mathematical discrepancy was found in the definitions or in the claims listed in A–E of the task: Riemann sign, Ricci contraction, 8πT normalization, k, f, A, ∂r, null/det/inverse, geodesy, the λ sign, the ψ definition, the Gröbner basis, R = 0, and 40 Γ.
