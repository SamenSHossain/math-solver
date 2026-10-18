Pure polynomial identities, taken from the definition blocks `NoHair_KerrNewmanEinstein_Ricci1`–`Ricci6` (lemmas `ricS_..`).

After unfolding, `RicS` is $\sum_\rho \partial_\rho\Gamma^\rho_{\nu\sigma}-\sum_{\rho,l}\Gamma^\rho_{\nu l}\Gamma^l_{\rho\sigma}$ in closed form. Its difference from `RicA` equals $c_1(k_1^2+k_2^2+k_3^2-1)+c_2(W(r^2+a^2k_3^2)-1)$, with explicit polynomial cofactors $c_1, c_2$ obtained by Gröbner-basis division (the leading terms $k_1^2$ and $Wr^2$ are coprime). `linear_combination` checks the identity.
