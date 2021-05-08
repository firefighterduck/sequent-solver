(* Actual sequent solver as prove automation *)
fun lists_have_intersect l1 l2 = List.exists (fn x1 => List.exists (fn x2 => x1 aconv x2) l2) l1

fun strip_prop ((Const (@{const_name "Pure.prop"},_))$((Const (@{const_name Trueprop}, _))$t)) = t
  | strip_prop t = t

fun innermost_imp ((Const (@{const_name "Pure.imp"},_))$_$((Const (@{const_name "Pure.imp"},_))$_$_)) = false
  | innermost_imp ((Const (@{const_name "Pure.imp"},_))$_$_) = true
  | innermost_imp _ = false

(* Recurse to the last subgoal (i.e. the one which will be solved first) *)
fun strip_imp t = case t of 
  ((Const (@{const_name "Pure.imp"},_))$((Const (@{const_name Trueprop},_))$goal)$t') =>
    if innermost_imp t then goal else strip_imp t' 
  | _ => t

fun mset_contains pred ((Const (@{const_name "add_mset"}, _))$element$mset) = 
    if pred element then true else mset_contains pred mset
  | mset_contains _ _ = false

fun is_bin_op bin_op trm = 
  (case trm of ((Const (name, _))$_$_) => bin_op=name
    | _ => false)

fun is_bot (Const (@{const_name "Bot"}, Type (@{type_name "formula"},_))) = true
  | is_bot _ = false
val contains_bot = mset_contains is_bot

fun BotL_applicable ((Const (@{const_name "SCp"}, _))$gamma$_) = contains_bot gamma
  | BotL_applicable _ = false

fun BotL_tac ctxt i thm = 
  if Thm.prop_of thm |> strip_prop |> strip_imp |> BotL_applicable
  then (resolve_tac ctxt @{thms BotL} THEN' asm_full_simp_tac ctxt) i thm
  else no_tac thm

fun get_elements ((Const (@{const_name "add_mset"}, _))$element$mset) =
    element :: (get_elements mset)
  | get_elements _ = []

fun extAx_applicable ((Const (@{const_name "SCp"}, _))$gamma$delta) = 
    lists_have_intersect (get_elements gamma) (get_elements delta)
  | extAx_applicable _ = false

fun extAx_tac ctxt i thm = 
  if Thm.prop_of thm |> strip_prop |> strip_imp |> extAx_applicable
  then (resolve_tac ctxt @{thms extended_Ax}  THEN' asm_full_simp_tac ctxt) i thm
  else no_tac thm

fun axioms_tac ctxt = extAx_tac ctxt ORELSE' BotL_tac ctxt

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

val is_and = is_bin_op @{const_name And}
val contains_and = mset_contains is_and

fun AndL_applicable ((Const (@{const_name "SCp"}, _))$gamma$_) = contains_and gamma
  | AndL_applicable _ = false

fun AndL_tac ctxt i = COND
  (AndL_applicable o strip_imp o strip_prop  o Thm.prop_of)
  (resolve_tac ctxt @{thms AndL} i)
  no_tac

fun AndR_applicable ((Const (@{const_name "SCp"}, _))$_$delta) = contains_and delta
  | AndR_applicable _ = false

fun AndR_tac ctxt i = COND
  (AndR_applicable o strip_imp o strip_prop  o Thm.prop_of)
  (resolve_tac ctxt @{thms AndR} i)
  no_tac

val is_or = is_bin_op @{const_name Or}
val contains_or = mset_contains is_or

fun OrL_applicable ((Const (@{const_name "SCp"}, _))$gamma$_) = contains_or gamma
  | OrL_applicable _ = false

fun OrL_tac ctxt i = COND
  (OrL_applicable o strip_imp o strip_prop  o Thm.prop_of)
  (resolve_tac ctxt @{thms OrL} i)
  no_tac

fun OrR_applicable ((Const (@{const_name "SCp"}, _))$_$delta) = contains_or delta
  | OrR_applicable _ = false

fun OrR_tac ctxt i = COND
  (OrR_applicable o strip_imp o strip_prop  o Thm.prop_of)
  (resolve_tac ctxt @{thms OrR} i)
  no_tac

val is_imp = is_bin_op @{const_name Imp}
val contains_imp = mset_contains is_imp

fun ImpL_applicable ((Const (@{const_name "SCp"}, _))$gamma$_) = contains_imp gamma
  | ImpL_applicable _ = false

fun ImpL_tac ctxt i = COND
  (ImpL_applicable o strip_imp o strip_prop  o Thm.prop_of)
  (resolve_tac ctxt @{thms ImpL} i)
  no_tac

fun ImpR_applicable ((Const (@{const_name "SCp"}, _))$_$delta) = contains_imp delta
  | ImpR_applicable _ = false

fun ImpR_tac ctxt i = COND 
  (ImpR_applicable o strip_imp o strip_prop  o Thm.prop_of)
  (resolve_tac ctxt @{thms ImpR} i)
  no_tac

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