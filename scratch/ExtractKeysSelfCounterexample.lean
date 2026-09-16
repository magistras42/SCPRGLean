import PRGExtension.Expression.SymbolicIndistinguishability
open PRG
-- counterexample to `extractKeys_hideEncrypted_self`
-- e = Enc (VarK 0) (VarK 1),  keys = {VarK 0}
def e : Expression (⦃𝕂⦄) := Expression.Enc (.VarK 0) (.VarK 1)
def keys : Finset (Expression 𝕂) := {Expression.VarK 0}
def Y := extractKeys (hideEncrypted keys e)
#eval ("hide keys e      ", reprStr (hideEncrypted keys e))
#eval ("Y = extractKeys  ", (Y.toList.map reprStr))
#eval ("hide Y e         ", reprStr (hideEncrypted Y e))
#eval ("extractKeys(hide Y e)", ((extractKeys (hideEncrypted Y e)).toList.map reprStr))
#eval ("Y ⊆ extractKeys(hide Y e)?", decide (Y ⊆ extractKeys (hideEncrypted Y e)))
