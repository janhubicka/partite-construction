# A genuinely partial decoder for complete-output mask relational graphs — 22 October 2026

Given an arbitrary OLD complete-mask relational interpretation E, the graph-value witness `HasWholeMaskValue E F x U` records one surjective distinct-root equality pattern of primitive input x and ONE complete output tuple whose output entries enumerate EXACTLY U. The independent `HasWholeMaskDomain E F x` records an active mask-domain tuple, whether or not a complete value tuple exists.

Define `wholeMaskPartialDecode E` as an `Option (Set V)`-valued genuine partial structure: choose `some U` from the complete output graph witnesses when any exists, otherwise return `none`. This does not confuse the states `some ∅` and `none` — a complete zero-output tuple supplies `some ∅`.

For an arbitrary inconsistent OLD graph the chosen U is not canonical and need not reflect all active OLD domains. The checked decoder laws therefore explicitly distinguish:
1. `func = none` exactly when no complete OLD output graph witness exists.
2. Given the uniqueness of all complete-value sets for this primitive input, `func = some U` iff U has an OLD complete-value witness.
3. A valid OLD complete-output tuple entails an active OLD domain relation, without any converse asserted at this stage.

The final B-covered target cross-equality-pattern value theorem supplies precisely the missing uniqueness requirement, while positive active domain completion and defined-empty coverage supply complementary existence requirements. Such a semantic decoder is not the strict mixed B-tree target completion and cannot repair that geometric step by itself.
