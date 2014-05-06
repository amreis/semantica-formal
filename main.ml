(** Main module for the task. Here the functions defined in other 
	modules are used to simulate and typecheck ASTs. *)

(** Include Typechecking capabilities *)
open Typechecker
include Typechecker;;
print_endline "Included typechecking functions."

(** Include Simulation cababilities *)
open Simulator
include Simulator;;
print_endline "Included simulation functions.";;


print_endline "Ready to go!";;
print_endline "Start tests...";;
					
let t3 = TmZero;;
let t2 = TmAbs("x", TyArr(TyId("X"), TyId("Y")), TmApp(TmVar("x"), TmZero)) ;;
let t1 = TmImplAbs("x", TmIsZero(TmVar("x"))) ;;
let t4 = TmImplAbs("x", TmImplAbs("y", TmImplAbs("z",
		TmApp(TmApp(TmVar("x"), TmVar("z")), TmApp(TmVar("y"), TmVar("z")))))) ;;

let t5 = TmCons(TmSucc(TmSucc(TmSucc(TmZero))),
			TmCons(TmZero, TmNil)) ;;
let t6 = (TmTail(t5));;
let t7 = TmAbs("x", TyList(TyId("X")), TmSucc(TmHead(TmVar("x"))));;

let t8 = TmAbs("x", TyNat, TmIf(TmIsZero(TmVar("x")), TmAbs("x", TyBool, 
							TmIf(TmVar("x"), TmSucc(TmZero), TmZero)),
							TmAbs("x", TyBool, TmIf(TmVar("x"), TmZero, TmSucc(TmZero)))));;
							

let nt1 = TmAbs("x", TyBool, TmIsZero(TmVar("x"))) ;;

let tLet = TmLet("double", TmImplAbs("f", TmImplAbs("a", TmApp(TmVar("f"), TmApp(TmVar("f"), TmVar("a"))))),
		   TmLet("a", TmApp(TmVar("double"), TmAbs("x", TyNat, TmSucc(TmSucc(TmVar("x"))))),
		   TmLet("b", TmApp(TmApp(TmVar("double"), TmAbs("x", TyBool, TmVar("x"))), TmFalse), TmApp(TmVar("a"), TmZero))));;

let ntLet = TmApp(TmApp(TmAbs("f", TyArr(TyId("X"), TyId("X")), 
					TmAbs("x", TyId("X"), TmLet("g", TmVar("f"), TmApp(TmVar("g"), TmZero)))),
					TmAbs("x", TyBool, TmIf(TmVar("x"), TmTrue, TmFalse))),
					TmTrue);;

let (t, c) = getConstraints ntLet ;;
printTerm ntLet ; print_string "Type: " ; printType t ; print_string "Constraints: \n" ; printConstraints c;;

let su = unify c ;;
let (tFinal, cFinal) = (applySubstType su t, applySubstConstr su c);;
print_endline "Final type:" ; print_string "\t" ; printType tFinal ;;
