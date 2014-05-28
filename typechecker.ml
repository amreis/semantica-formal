(** Module for the typechecking functions *)

open Langtypes
include Langtypes


let constraintToString (c : constr) : string = 
	let (t1, t2) = c in
	(typeToString t1) ^ " = " ^ (typeToString t2)
	
let printConstraints (c : constr list) : unit = 
	print_endline "{ " ; 
	(List.iter (fun x -> print_endline ("\t" ^ (constraintToString x))) c) ;
	print_endline "}" ;;

let printSubst (s : subst) : unit = 
	print_string "[";
	let rec substToString su = 
		match su with
		[] -> ""
		| ((ty1,ty2)::rest) ->
			(typeToString ty1 ^ " => " ^ typeToString ty2)
				^ (if rest = [] then " ]" else ", ") ^
				  (substToString rest)
	in print_endline (substToString s) 
			
(** Function that determines whether a Type Variable occurs in another 
	type *)
let rec occursin var t2 = 
	match t2 with
		TyNat | TyBool -> false
		| TyId(v2) -> var = v2
		| TyList(t1) -> occursin var t1
		| TyArr(s1, s2) ->
			(occursin var s1) || (occursin var s2)

(** Function that applies a substitution to a type *)
let rec applySubstType (s : subst) (t : ty) : ty = 
	let rec applyS (ty : ty) (su : (ty*ty)) =
		match ty with
		| TyNat as x -> x
		| TyBool as x -> x
		| TyList(t1) -> TyList(applyS t1 su)
		| TyArr(t1,t2) -> TyArr((applyS t1 su), (applyS t2 su))
		| TyId(var) -> 
			match su with 
			| (TyId(var1), t1) ->
				if var = var1 then t1 else TyId(var)
			| _ -> failwith "Never happens"		
		in
		List.fold_left applyS t s	

(** Function that applies a substitution to a list of constraints *)
let applySubstConstr (s : subst) (c: constr list) : constr list=
	List.map (fun elem -> let (t1,t2) = elem in
				((applySubstType s t1),(applySubstType s t2))) c
				
(** Function that applies a substitution to a context *)
let applySubstCtx (s: subst) (c : context) : context = 
	List.map (fun elem -> let (var, TypeScheme(gens, ty)) = elem in
					(var, TypeScheme(gens, applySubstType s ty))) c
					
(** Exception raised when a cyclic substitution like [X => X->X] would
	be created *)
exception CyclicSubstitution
(** Exception raised when an AST is invalid, because it generated unsolvable
	constraints *)
exception NotUnifiable

(** Function that unifies a constraint list by generating a substitution *)
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

(** Exception raised when the type of an identifier cannot be found in the
	context *)
exception TypeNotFound
(** Exception raised when an AST is not typable *)
exception NotTypable

(** Function that removes duplicates from a list. *)
let removeDuplicates list = 
	let rec removeDuplicates' l1 acc = 
		match l1 with
		[] -> acc
		| (hd::tl) -> if List.mem hd acc then removeDuplicates' tl acc
					  else removeDuplicates' tl (hd::acc)
	in removeDuplicates' list []  
	
(** Function to determine which variables in a type can be generalized in
	the type scheme. Used to type the polymorphic let construction *)
let generalizeVars (t : ty) (ctx : context) : string list =
	let rec findVars (ty : ty) =
		match ty with 
		| TyNat -> []
		| TyBool -> []
		| TyArr(t1,t2) -> 
				removeDuplicates (List.concat [findVars t1; findVars t2])
		| TyList(t1) -> findVars t1
		| TyId(var) -> [var]
	in
	let rec isInContext var ctx = 
		match ctx with
		[] -> false
		| ((v,TypeScheme(vars,ty))::rest) ->
			match vars with 
			[] ->	occursin var ty || isInContext var rest
			| _ -> isInContext var rest
	in
	let result = 
		List.filter (fun var -> not (isInContext var ctx)) (findVars t)
	in result


(** Function that, given a scheme, generates a type based on it, using a 
	variable name generator *)
let rec typeFromScheme (genVars : string list) (baseType : ty) (nxtvar : uvargenerator) =
	
	let rec createSubst gVars substAcc varGen =
	match gVars with
	[] -> (substAcc, varGen)
	| (hd::tl) ->
		let NextUVar(newvar, nxt) = varGen() in
		createSubst tl ((TyId(hd), TyId(newvar))::substAcc) nxt
	
	in
	let (subst, nextvar) = (createSubst genVars [] nxtvar) in
	(* TODO: Testar se precisa desse List.rev. Acho que não *)
	((applySubstType subst baseType), nextvar)
		
(** Function that gets the type of a variable from the context. May raise
	TypeNotFound exception. *)
let rec getTypeFromContext (ctx : context) (var : string) (nxtvar : uvargenerator) =
	match ctx with
		[] -> raise TypeNotFound
		| ((v,t)::rest) ->
			if var = v then match t with
				TypeScheme(generalized, tSch) -> 
					typeFromScheme generalized tSch nxtvar
			else getTypeFromContext rest var nxtvar
(** Generate a set of constraints for the AST to be well typed *)
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
			 	let (tyT1, nxt1, constr1) = genConstraints t1 ((id, TypeScheme([],idType))::ctx) nextuvar in
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
		 			let (tyVar, nxt1) = getTypeFromContext ctx id nextuvar
			 		in (tyVar, nxt1, [])
		 		with TypeNotFound -> raise NotTypable
		 		end
			| TmImplAbs(id, t1) ->
				let NextUVar(nxtvar, nxt1) = nextuvar() in
				let (tyT1, nxt2, constr1) = genConstraints t1 ((id, TypeScheme([],TyId(nxtvar)))::ctx) nxt1 in
				(TyArr(TyId(nxtvar), tyT1), nxt2, constr1)
			| TmLet(id, t1, t2) ->
				let (t1T, nxt1, t1C) = genConstraints t1 ctx nextuvar in
				let t1S = unify t1C in
				let (newCtx, newT1T) = (applySubstCtx t1S ctx, applySubstType t1S t1T) in
				print_endline "Typing sub-expression " ; printTerm t1;
				print_endline "Type: " ; printType t1T ; 
				print_endline "Constraints: "; printConstraints t1C;
				let genVars = generalizeVars newT1T newCtx in
				let (tyT2, nxt2, constr2) = genConstraints t2 ((id, TypeScheme(genVars,newT1T))::newCtx) nxt1 in
				(tyT2, nxt2, List.concat[ t1C; constr2 ])
			| TmNil ->
				let NextUVar(nxtvar, nxt1) = nextuvar() in
				(TyList(TyId(nxtvar)), nxt1, [])
			| TmCons(t1, t2) ->
				let (tyT1, nxt1, constr1) = genConstraints t1 ctx nextuvar in
				let (tyT2, nxt2, constr2) = genConstraints t2 ctx nxt1 in
				(TyList(tyT1), nxt2, List.concat [(tyT2, TyList(tyT1))::constr1 ; constr2] )
				
			
			| TmHead(t1) ->
				let (tyT1, nxt1, constr1) = genConstraints t1 ctx nextuvar in
				let NextUVar(nxtvar, nxt2) = nxt1() in
				(TyId(nxtvar), nxt2, (tyT1, TyList(TyId(nxtvar)))::constr1)
			| TmTail(t1) ->
				let (tyT1, nxt1, constr1) = genConstraints t1 ctx nextuvar in
				let NextUVar(nxtvar, nxt2) = nxt1() in
				(TyList(TyId(nxtvar)), nxt2, (tyT1, TyList(TyId(nxtvar)))::constr1)
			| TmRaise ->
				let NextUVar(var, nxt1) = nextuvar() in
				(TyId(var), nxt1, [])
			| TmTry(t1,t2) ->
				let (tyT1, nxt1, constr1) = genConstraints t1 ctx nextuvar in
				let (tyT2, nxt2, constr2) = genConstraints t1 ctx nxt1 in
				(tyT2, nxt2, List.concat[ (tyT1,tyT2)::constr1 ; constr2 ])
			| TmLetRec(id,ty,t1,t2) ->
				let (tyT1, nxt1, constr1) = genConstraints t1 ((id, TypeScheme([], ty))::ctx) nextuvar in
				let (tyT2, nxt2, constr2) = genConstraints t2 ((id, TypeScheme([], ty))::ctx) nxt1 in
				(tyT2, nxt2, List.concat [ (tyT1,ty)::constr1; constr2; ])
			| TmImplLetRec(id,t1,t2) ->
				let NextUVar(var1, nxt1) = nextuvar() in
				let NextUVar(var2, nxt2) = nxt1() in
				let ty = TyArr(TyId(var1), TyId(var2)) in
				let (tyT1, nxt3, constr1) = genConstraints t1 ((id, TypeScheme([], ty))::ctx) nxt2 in
				print_endline "Typing sub-expression " ; printTerm t1;
				print_endline "Type: " ; printType tyT1 ; 
				print_endline "Constraints: "; printConstraints constr1;
				let t1S = unify constr1 in
				let (newCtx, newTyT1) = (applySubstCtx t1S ctx, applySubstType t1S tyT1) in
				let genVars = generalizeVars newTyT1 newCtx in
				let (tyT2, nxt4, constr2) = genConstraints t2 ((id, TypeScheme(genVars, newTyT1))::ctx) nxt3 in
				(tyT2, nxt4, List.concat[constr1; constr2])
	in
	let (t, _, c) = genConstraints t [] uvargen
	in (t,c)

