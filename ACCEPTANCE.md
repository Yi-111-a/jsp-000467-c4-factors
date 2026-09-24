# ACCEPTANCE — JSP-000467 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000467

## Exact original question (English)

> What minimum degree forces a spanning collection of vertex-disjoint four-cycles?

Accepted resolution: Wang (Wa10), Graphs Combin. (2010) — Proof of the Erdős–Faudree Conjecture on Quadrilaterals.

## Required Lean theorem name(s)

| Lean name | Intended statement |
|---|---|
| `spanning_c4_factors_min_degree` | Wa10: the precise minimum-degree threshold forcing a spanning collection of vertex-disjoint 4-cycles (exact constant/parity as in Wa10). |

## Checklist

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit`
- [ ] Headline theorem proved (not True placeholder)
- [ ] Public repo HEAD full SHA; formalization.yaml / ATTRIBUTION name Yi-111-a
