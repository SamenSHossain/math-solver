**Complete proof: no `sorry` anywhere in the chain; axioms `propext`, `Classical.choice`, `Quot.sound`.**

The solution imports:
- the definition blocks `NoHair_KerrNewmanEinstein_Base` (atoms, closed forms, the calculus `HasCP`) and `…_Atoms` (metric and inverse metric);
- eight Proved platform theorems: `NoHair.KNE.thm_christoffel`, `thm_div_one`, `thm_div_two`, `thm_div_three`, `thm_ricci_a`, `thm_ricci_b`, `thm_ricci_c`, `thm_maxwell`.

These theorems are proved from the further blocks `Christoffel`, `Div1`–`Div4`, `Ricci1`–`Ricci6`, `MaxwellF` and `MaxwellT`.

**Atoms.** On the open set $U=\{r>0\}$, work with $r$, $k_1,k_2,k_3$ and $W=1/(r^2+a^2k_3^2)$. They satisfy $k_1^2+k_2^2+k_3^2=1$ (from $r^4-(\rho^2-a^2)r^2-a^2z^2=0$) and $W(r^2+a^2k_3^2)=1$. The coordinates are recovered as $x=rk_1-ak_2$, $y=ak_1+rk_2$, $z=rk_3$. The partials of the atoms are polynomials in the atoms; they are derived from implicit differentiation of the quartic. In these atoms the profile is $f=(2mr-e^2)W$ and the potential factor is $H=erW$.

**Calculus.** A small predicate `HasCP f z d` says that $f$ is differentiable at $z$ with coordinate partials $d$. It is closed under $+,-,\times,/,(\cdot)^n$ and constants, and is proved along lines with `HasDerivAt`. From it:
- `cp_metric` gives $\partial_j g_{lk}$;
- with the inverse $g^{-1}=\eta-f\,k^\sharp k^{\sharp T}$ (valid because $k$ is null), `chr_closed` gives every $\Gamma^i_{jk}$ on $U$ as an explicit polynomial in the atoms. These are 40 polynomial identities.

**Curvature at $y$.**
- `ricci` unfolds to $\sum_\rho\partial_\rho\Gamma^\rho_{\nu\sigma}-\sum_\rho\partial_\nu\Gamma^\rho_{\rho\sigma}+\sum_{\rho,l}(\Gamma\Gamma-\Gamma\Gamma)$.
- The trace $\sum_\rho\Gamma^\rho_{\rho\sigma}$ vanishes identically on $U$ (det $g=-1$), so its derivative vanishes. This uses differentiability of the closed forms and `fderiv_fun_sum`.
- The divergences $\partial_\rho\Gamma^\rho_{\nu\sigma}$ come from explicit `HasCP` derivations of the closed forms (`Div1`–`Div4`). The time direction is handled by translation invariance.
- The resulting Ricci formula equals the closed-form `RicA` (`Ricci1`–`Ricci6`; ten components, the rest by symmetry), and the scalar curvature is $0$. Hence $G_{\mu\nu}=R_{\mu\nu}$.

**Maxwell side.**
- $F=dA$ with $A=Hk$ gives the closed-form `FA` (`MaxwellF`). Raising with $g^{-1}$ gives `FupA`, and contracting gives the invariant `FFA`.
- `maxwellSource` reduces to `TS`, and `TS = RicA` (`MaxwellT`).

**How the identities are proved.** Every algebraic step is a polynomial identity in $r,k_1,k_2,k_3,W,a,m,e$ modulo the two relations above. Each is closed by `linear_combination c₁ * hrel + c₂ * hW`. The cofactors come from division by the Gröbner basis {$k_1^2+k_2^2+k_3^2-1$, $W(r^2+a^2k_3^2)-1$}, whose leading terms are coprime, computed in SymPy. The closed forms come from a symbolic computation that mirrors the Lean definitions. As an independent check, the same computation reproduces $G_{\mu\nu}=8\pi T_{\mu\nu}$ and $R=0$ symbolically.
