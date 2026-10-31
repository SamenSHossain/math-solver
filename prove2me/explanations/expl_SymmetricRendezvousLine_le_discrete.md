We prove that the symmetric rendezvous value on the line is at most its discrete counterpart:

$$R \le R_{\mathrm{disc}},$$

where $R=\inf_S E(S,S)$ ranges over all mixed strategies $S$ and $R_{\mathrm{disc}}$ is the infimum of the same quantity $E(S,S)$ over the mixed strategies all of whose realised paths are integer zigzags (full speed, direction changes only at integer times).

**Proof idea.** The two values are infima of the same function $S\mapsto E(S,S)$; the first over the whole class of mixed strategies, the second over a subclass. An infimum can only decrease when the index set grows.

**Argument.** Let $S$ be any mixed strategy all of whose paths are integer zigzags. Then $S$ is in particular a mixed strategy, so by definition of $R$ as an infimum,

$$R \le E(S,S).$$

Since this holds for every such $S$, the characteristic property of the infimum defining $R_{\mathrm{disc}}$ (the greatest lower bound of the values $E(S,S)$ over the restricted class) gives $R \le R_{\mathrm{disc}}$. In Lean the discrete value is a doubly indexed infimum, over strategies $S$ and over proofs that every path of $S$ is an integer zigzag, so the statement is `le_iInf₂` applied to the bound `iInf_le` furnished by the definition of $R$.

This is the trivial half of the Han–Du–Vera–Zuluaga reduction $R = R_{\mathrm{disc}}$; the substantive half, $R_{\mathrm{disc}} \le R$, is their dominance theorem for integer-time full-speed strategies.
