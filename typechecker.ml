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
		| TyList(t1) -> (typeToString t1) ^ " list"
		| TyArr(t1, t2) -> 
			"(" ^ (typeToString t1) ^ " -> " ^ (typeToString t2) ^ ")"

let printType (t : ty) : unit =  
	print_endline (typeToString t)
let rec termToString (t:term) = match t with
	| TmZero -> "0"
	| TmTrue -> "true"
	| TmFalse -> "false"
	| TmSucc(t1) -> "(succ " ^ (termToString t1) ^ ")"
	| TmPred(t1) -> "(pred " ^ (termToString t1) ^ ")"
	| TmIsZero(t1) -> "(iszero " ^ (termToString t1) ^ ")"
	| TmIf(t1,t2,t3) -> "(if " ^ (termToString t1) ^ " then " ^
							termToString t2 ^ " else " ^ termToString t3 ^ ")"
	| TmAbs(id,typ,t1) -> "(fn " ^ id ^ ":" ^ typeToString typ ^ " => " 
								^ termToString t1 ^ ")"
	| TmApp(t1, t2) -> "( " ^ termToString t1 ^ " " ^ termToString t2 ^ " )"
	| TmVar(id) -> id
	| TmImplAbs(id,t1) -> "(fn " ^ id ^ " => " ^ termToString t1 ^ ")"
	| TmCons(t1, t2) -> "(" ^ termToString t1 ^ "::" ^ termToString t2 ^ ")"
	| TmNil -> "[]"
	| TmHead(t) -> "(hd " ^ termToString t ^ ")"
	| TmTail(t) -> "(tl " ^ termToString t ^ ")"

let printTerm (t : term) =
	print_endline (termToString t)

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
			TmZero -> (TyNat, nextuvar, [])
			| TmTrue -> (TyBool, nextuvar, [])
			| TmFalse -> (TyBool, nextuvar, [])
			| TmSucc(t1) -> 
				let (tyT1, nxt1, constr) = genConstraints t1 ctx nextuvar
				in
				(TyNat, nxt1, (tyT1, TyNat)::constr)
			| TmPred(t1) ->
				let (tyT1, nxt1, constr) = genConstraints t1 ctx nextuvar
				in
				(TyNat, nxt1, (tyT1, TyNat)::constr)
			| TmIsZero(t1) ->
				let (tyT1, nxt1, constr) = genConstraints t1 ctx nextuvar
				in
				(TyBool, nxt1, (tyT1, TyNat)::constr)
			| TmIf(t1, t2, t3) ->
				let (tyT1, nxt1, constr1) = genConstraints t1 ctx nextuvar in
				let (tyT2, nxt2, constr2) = genConstraints t2 ctx nxt1 in
				let (tyT3, nxt3, constr3) = genConstraints t3 ctx nxt2 in
				(tyT3, nxt3, 
				List.concat [(tyT1,TyBool)::(tyT2,tyT3)::constr1 ;
							 constr2 ; constr3 ] )
			| TmAbs(id, idType, t1) ->
			 	let (tyT1, nxt1, constr1) = genConstraints t1 ((id, idType)::ctx) nextuvar in
			 	(TyArr(idType, tyT1), nxt1, constr1)
			 	
		 	| TmApp(t1, t2) ->
		 		let (tyT1, nxt1, constr1) = genConstraints t1 ctx nextuvar in
		 		let (tyT2, nxt2, constr2) = genConstraints t2 ctx nxt1 in
		 		let NextUVar(nxtvar, nxt3) = nxt2() in
		 		(TyId(nxtvar), nxt3, 
		 			List.concat [(tyT1, TyArr(tyT2, TyId(nxtvar)))::constr1 ; constr2] )
			
		 	| TmVar(id) ->
		 		begin
		 		try
		 			let tyVar = getTypeFromContext ctx id
			 		in (tyVar, nextuvar, [])
		 		with TypeNotFound -> raise NotTypable
		 		end
		 	| TmImplAbs(id, t1) ->
				let NextUVar(nxtvar, nxt1) = nextuvar() in
				let (tyT1, nxt2, constr1) = genConstraints t1 ((id, TyId(nxtvar))::ctx) nxt1 in
				(TyArr(TyId(nxtvar), tyT1), nxt2, constr1)
				
		 	| TmCons(t1, t2) ->
				let (tyT1, nxt1, constr1) = genConstraints t1 ctx nextuvar in
				let (tyT2, nxt2, constr2) = genConstraints t2 ctx nxt1 in
				(TyList(tyT1), nxt2, List.concat [(tyT2, TyList(tyT1))::constr1 ; constr2] )
				
			| TmNil ->
				let NextUVar(nxtvar, nxt1) = nextuvar() in
				(TyList(TyId(nxtvar)), nxt1, [])
			| TmHead(t1) ->
				let (tyT1, nxt1, constr1) = genConstraints t1 ctx nextuvar in
				let NextUVar(nxtvar, nxt2) = nxt1() in
				(TyId(nxtvar), nxt2, (tyT1, TyList(TyId(nxtvar)))::constr1)
			| TmTail(t1) ->
				let (tyT1, nxt1, constr1) = genConstraints t1 ctx nextuvar in
				let NextUVar(nxtvar, nxt2) = nxt1() in
				(TyList(TyId(nxtvar)), nxt2, (tyT1, TyList(TyId(nxtvar)))::constr1)
			
	in
	let (t, _, c) = genConstraints t [] uvargen
	in (t,c)
	
	
let rec occursin var t2 = 
	match t2 with
		TyNat | TyBool -> false
		| TyId(v2) -> var = v2
		| TyList(t1) -> occursin var t1
		| TyArr(s1, s2) ->
			(occursin var s1) || (occursin var s2)

let rec applySubstType (s : subst) (t : ty) : ty = 
	let rec applyS (su : (ty*ty)) (ty : ty) =
		match ty with
		| TyNat as x -> x
		| TyBool as x -> x
		| TyList(t1) -> TyList(applyS su t1)
		| TyArr(t1,t2) -> TyArr((applyS su t1), (applyS su t2))
		| TyId(var) -> 
			match su with 
			| (TyId(var1), t1) ->
				if var = var1 then t1 else TyId(var)
			| _ -> failwith "Never happens"		
		in
		List.fold_right applyS s t
		
let applySubstConstr (s : subst) (c: constr list) : constr list=
	List.map (fun elem -> let (t1,t2) = elem in
				((applySubstType s t1),(applySubstType s t2)))
			 c
exception CyclicSubstitution
exception NotUnifiable


let rec unify (c: constr list) : subst = 
	match c with
	[] -> []
	| ((s,t)::c') ->
		match (s,t) with
			(x,y) when x = y -> unify c'
			|(TyId(var), t) ->
				if not (occursin var t) then
					let subst = (TyId(var), t) in
					subst::(unify (applySubstConstr [subst] c'))
				else raise CyclicSubstitution
			|(s, TyId(var)) ->
				if not (occursin var s) then
					let subst = (TyId(var), s) in
					subst::(unify (applySubstConstr [subst] c'))
				else raise CyclicSubstitution
			|(TyArr(s1,s2), TyArr(t1,t2)) ->
				unify ((s1,t1)::(s2,t2)::c')
			|(TyList(s1), TyList(t1)) ->
				unify ((s1,t1)::c')
			| _ -> raise NotUnifiable

