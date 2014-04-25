open Langtypes
include Langtypes

type nextuvar = NextUVar of string * uvargenerator
	and uvargenerator = unit -> nextuvar

let uvargen =
	let rec f n () = NextUVar("?X_" ^ string_of_int n, f (n+1))
	in f 0

let rec typeToString t = match t with
		TyNat -> "Nat"
		| TyBool -> "Bool"
		| TyId(var) -> var
		| TyArr(t1, t2) -> 
			"(" ^ (typeToString t1) ^ " -> " ^ (typeToString t2) ^ ")"

let printType (t : ty) : unit =  
	print_endline (typeToString t)

let constraintToString (c : constr) : string = 
	let (t1, t2) = c in
	(typeToString t1) ^ " = " ^ (typeToString t2)
	
let printConstraints (c : constr list) : unit = 
	print_endline "{ " ; 
	(List.iter (fun x -> print_endline ("\t" ^ (constraintToString x))) c) ;
	print_endline "}" ;;

exception TypeNotFound
exception NotTypable

let rec getTypeFromContext (ctx : context) (var : string) : ty =
	match ctx with
		[] -> raise TypeNotFound
		| ((v,t)::rest) ->
			if var = v then t else getTypeFromContext rest var

let getConstraints (t : term) : ty * (constr list)= 
	let rec genConstraints (t : term) (ctx : context) (nextuvar : uvargenerator) : ty * uvargenerator * (constr list) = 
		match t with
			TmZero(_) -> (TyNat, nextuvar, [])
			| TmTrue(_) -> (TyBool, nextuvar, [])
			| TmFalse(_) -> (TyBool, nextuvar, [])
			| TmSucc(_, t1) -> 
				let (tyT1, nxt1, constr) = genConstraints t1 ctx nextuvar
				in
				(TyNat, nxt1, (tyT1, TyNat)::constr)
			| TmPred(_, t1) ->
				let (tyT1, nxt1, constr) = genConstraints t1 ctx nextuvar
				in
				(TyNat, nxt1, (tyT1, TyNat)::constr)
			| TmIsZero(_, t1) ->
				let (tyT1, nxt1, constr) = genConstraints t1 ctx nextuvar
				in
				(TyBool, nxt1, (tyT1, TyNat)::constr)
			| TmIf(_, t1, t2, t3) ->
				let (tyT1, nxt1, constr1) = genConstraints t1 ctx nextuvar in
				let (tyT2, nxt2, constr2) = genConstraints t2 ctx nxt1 in
				let (tyT3, nxt3, constr3) = genConstraints t3 ctx nxt2 in
				(tyT3, nxt3, 
				List.concat [(tyT1,TyBool)::(tyT2,tyT3)::constr1 ;
							 constr2 ; constr3 ] )
			| TmAbs(_, id, idType, t1) ->
			 	let (tyT1, nxt1, constr1) = genConstraints t1 ((id, idType)::ctx) nextuvar in
			 	(TyArr(idType, tyT1), nxt1, constr1)
			 	
		 	| TmImplAbs(_, id, t1) ->
				let NextUVar(nxtvar, nxt1) = nextuvar() in
				let (tyT1, nxt2, constr1) = genConstraints t1 ((id, TyId(nxtvar))::ctx) nxt1 in
				(TyArr(TyId(nxtvar), tyT1), nxt2, constr1) 	
		 	
		 	| TmApp(_, t1, t2) ->
		 		let (tyT1, nxt1, constr1) = genConstraints t1 ctx nextuvar in
		 		let (tyT2, nxt2, constr2) = genConstraints t2 ctx nxt1 in
		 		let NextUVar(nxtvar, nxt3) = nxt2() in
		 		(TyId(nxtvar), nxt3, 
		 			List.concat [(tyT1, TyArr(tyT2, TyId(nxtvar)))::constr1 ; constr2] )
		 				 	
		 	| TmVar(_, id) ->
		 		let tyVar = getTypeFromContext ctx id
		 		in (tyVar, nextuvar, [])
		 		
	in
	let (t, _, c) = genConstraints t [] uvargen
	in (t,c)
	
let t3 = TmZero("");;
let t2 = TmAbs("", "x", TyArr(TyId("X"), TyId("Y")), TmApp("", TmVar("", "x"), TmZero(""))) ;;
let t1 = TmImplAbs("", "x", TmIsZero("", TmVar("","x"))) ;;
print_endline "Constraints for t1:" ;
let (t, c) = getConstraints t1 in
printConstraints c ;
print_endline "Type for t1:" ;
printType t ;;


