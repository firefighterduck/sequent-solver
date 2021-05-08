(* Actual sequent solver as prove automation *)

(* Auxiliary functions *)
fun lists_have_intersect l1 l2 = List.exists (fn x1 => List.exists (fn x2 => x1 aconv x2) l2) l1

fun strip_prop ((Const (@{const_name "Pure.prop"},_))$((Const (@{const_name Trueprop}, _))$t)) = t
  | strip_prop t = t

fun is_innermost_imp ((Const (@{const_name "Pure.imp"},_))$_$((Const (@{const_name "Pure.imp"},_))$_$_))
       = false
  | is_innermost_imp ((Const (@{const_name "Pure.imp"},_))$_$_) = true
  | is_innermost_imp _ = false

(* Recurse to the last subgoal (i.e. the one which will be solved first) *)
fun strip_imp t = case t of 
  ((Const (@{const_name "Pure.imp"},_))$((Const (@{const_name Trueprop},_))$goal)$t') =>
    if is_innermost_imp t then goal else strip_imp t' 
  | _ => t

fun mset_contains pred ((Const (@{const_name "add_mset"}, _))$element$mset) = 
    if pred element then true else mset_contains pred mset
  | mset_contains _ _ = false

fun is_bin_op bin_op trm = case trm of 
  ((Const (name, _))$_$_) => bin_op=name
  | _ => false

fun rule_applicableL rule_bin_op t = case t of 
  ((Const (@{const_name "SCp"}, _))$gamma$_) => 
    mset_contains (is_bin_op rule_bin_op) gamma
  | _ => false

fun rule_applicableR rule_bin_op t = case t of 
  ((Const (@{const_name "SCp"}, _))$_$delta) => 
    mset_contains (is_bin_op rule_bin_op) delta
  | _ => false

fun rule_tacL rule_thm rule_bin_op ctxt i = COND
  ((rule_applicableL rule_bin_op) o strip_imp o strip_prop  o Thm.prop_of)
  (resolve_tac ctxt [rule_thm] i)
  no_tac

fun rule_tacR rule_thm rule_bin_op ctxt i = COND
  ((rule_applicableR rule_bin_op) o strip_imp o strip_prop  o Thm.prop_of)
  (resolve_tac ctxt [rule_thm] i)
  no_tac

(* Rule BotL *)
fun is_bot (Const (@{const_name "Bot"}, Type (@{type_name "formula"},_))) = true
  | is_bot _ = false
val contains_bot = mset_contains is_bot
fun BotL_applicable ((Const (@{const_name "SCp"}, _))$gamma$_) = contains_bot gamma
  | BotL_applicable _ = false
fun BotL_tac ctxt i = COND
  (BotL_applicable o strip_imp o strip_prop  o Thm.prop_of)
  ((resolve_tac ctxt @{thms BotL}  THEN' asm_full_simp_tac ctxt) i)
  no_tac

(* Rule extendedAx *)
fun get_elements ((Const (@{const_name "add_mset"}, _))$element$mset) =
    element :: (get_elements mset)
  | get_elements _ = []
fun extAx_applicable ((Const (@{const_name "SCp"}, _))$gamma$delta) = 
    lists_have_intersect (get_elements gamma) (get_elements delta)
  | extAx_applicable _ = false
fun extAx_tac ctxt i = COND
  (extAx_applicable o strip_imp o strip_prop  o Thm.prop_of)
  ((resolve_tac ctxt @{thms extended_Ax}  THEN' asm_full_simp_tac ctxt) i)
  no_tac

(* Rules NotL/NotR *)
fun is_not ((Const (@{const_name Not}, _))$_) = true
  | is_not _ = false
val contains_not = mset_contains is_not
fun NotL_applicable ((Const (@{const_name "SCp"}, _))$gamma$_) = contains_not gamma
  | NotL_applicable _ = false
fun NotL_tac ctxt i = COND
  (NotL_applicable o strip_imp o strip_prop  o Thm.prop_of)
  (resolve_tac ctxt @{thms NotL} i)
  no_tac
fun NotR_applicable ((Const (@{const_name "SCp"}, _))$_$delta) = contains_not delta
  | NotR_applicable _ = false
fun NotR_tac ctxt i = COND
  (NotR_applicable o strip_imp o strip_prop  o Thm.prop_of)
  (resolve_tac ctxt @{thms NotR} i)
  no_tac

(* Rules AndL/AndR/OrL/OrR/ImpL/ImpR *)
val AndL_tac = rule_tacL @{thm AndL} @{const_name And}
val AndR_tac = rule_tacR @{thm AndR} @{const_name And}
val OrL_tac = rule_tacL @{thm OrL} @{const_name Or}
val OrR_tac = rule_tacR @{thm OrR} @{const_name Or}
val ImpL_tac = rule_tacL @{thm ImpL} @{const_name Imp}
val ImpR_tac = rule_tacR @{thm ImpR} @{const_name Imp}

fun solver_step_tac ctxt = (FIRST' [
    CHANGED o asm_full_simp_tac ctxt,
    BotL_tac ctxt,
    NotL_tac ctxt, 
    NotR_tac ctxt, 
    AndL_tac ctxt,
    OrR_tac ctxt,
    ImpR_tac ctxt,
    extAx_tac ctxt, 
    (* Splitting tacs at the end to keep proof trees small *)
    ImpL_tac ctxt,
    AndR_tac ctxt,
    OrL_tac ctxt
])

fun solver_tac ctxt = REPEAT (CHANGED (TRYALL (solver_step_tac ctxt)))