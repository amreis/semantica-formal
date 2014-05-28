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
let tst_letRecPoly = TmImplLetRec("double", TmImplAbs("f", TmImplAbs("a", TmApp(TmVar("f"), TmApp(TmVar("f"), TmVar("a"))))),
		   TmLet("a", TmApp(TmVar("double"), TmAbs("x", TyNat, TmSucc(TmSucc(TmVar("x"))))),
		   TmLet("b", TmApp(TmApp(TmVar("double"), TmAbs("x", TyBool, TmVar("x"))), TmFalse), TmApp(TmVar("a"), TmZero))));;
let ntLet = TmApp(TmApp(TmAbs("f", TyArr(TyId("X"), TyId("X")), 
					TmAbs("x", TyId("X"), TmLet("g", TmVar("f"), TmApp(TmVar("g"), TmZero)))),
					TmAbs("x", TyBool, TmIf(TmVar("x"), TmTrue, TmFalse))),
					TmTrue);;
let length = TmLetRec("l", TyArr(TyList(TyId("X")), TyArr(TyNat, TyNat)), 
			 TmImplAbs("x", TmImplAbs("acc", TmTry(TmLet("h", TmHead(TmVar("x")), TmSucc(TmApp(TmApp(TmVar("l"), TmTail(TmVar("x"))), TmSucc(TmVar("acc"))))),
									TmVar("acc")))),
			 TmApp(TmApp(TmVar("l"), TmCons(TmZero,TmCons(TmZero,TmCons(TmZero,TmNil)))), TmZero)) ;;
let implLength = TmImplLetRec("l",
			 TmImplAbs("x", TmImplAbs("acc", TmTry(TmLet("h", TmHead(TmVar("x")), TmSucc(TmApp(TmApp(TmVar("l"), TmTail(TmVar("x"))), TmVar("acc")))),
									TmVar("acc")))),
			 TmApp(TmApp(TmVar("l"), TmCons(TmZero,TmCons(TmZero,TmCons(TmZero,TmNil)))), TmZero)) ;;
			 
let giantTerm = TmIf(TmIsZero(implLength), TmSucc(tLet), TmSucc(tst_letRecPoly));;

let simpleApp = TmApp(TmImplAbs("x", TmSucc(TmVar("x"))), TmZero);;

let listTerm = TmHead(TmCons(TmSucc(TmZero), 
				TmCons(
				TmApp(TmImplAbs("x", TmIf(TmIsZero(TmVar("x")), TmSucc(TmVar("x")), TmVar("x"))), TmSucc(TmSucc(TmZero))), TmNil))) ;;
let tryTerm = TmTry(TmHead(TmNil), TmTry(TmTail(TmNil), TmTry(TmHead(TmCons(TmTrue,TmNil)), TmNil)));;
let dummyRec = TmImplLetRec("x", TmImplAbs("n", TmIf(TmIsZero(TmVar("n")), TmSucc(TmZero), TmApp(TmVar("x"), TmPred(TmVar("n"))))),
				TmApp(TmVar("x"), TmSucc(TmSucc(TmSucc(TmZero)))));;

let (t, c) = getConstraints giantTerm ;;
printTerm giantTerm ; print_string "Type: " ; printType t ; print_string "Constraints: \n" ; printConstraints c;;

let su = unify c ;;
print_endline "Solving substitution: ";;
printSubst su;;
let (tFinal, cFinal) = (applySubstType su t, applySubstConstr su c);;
print_endline "Final type:" ; print_string "\t" ; printType tFinal ;;
let r = eval giantTerm uvargen in
printTerm (r)

