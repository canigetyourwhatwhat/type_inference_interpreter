(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

let rec apply_subst (t : ty) (s : subst) : ty =
    match t with
    | TyName(name) -> t
    | TyVar(var1) ->
        let sub = List.tryFind(fun (var, _) -> var = var1) s
        match sub with
        | None -> t
        | Some(_, ty) -> ty
    | TyTuple(nums) -> TyTuple(List.map(fun item -> apply_subst item s) nums)
    | TyArrow(ty1, ty2) -> TyArrow(apply_subst ty1 s, apply_subst ty2 s)
    
let compose_subst (s1 : subst) (s2 : subst) : subst =
    List.fold(fun acc (var, ty) -> (var,(apply_subst ty s1))::acc) s1 s2

let rec unify (t1 : ty) (t2 : ty) : subst =
    match t1, t2 with
    | TyName(name1), TyName(name2) -> if name1 = name2 then [] else type_error "wrong unification: cannot unify type variable: %s and %s" name1 name2
    | TyVar(var1), ty | ty, TyVar(var1) -> if t1 = t2 then [] else [(var1, ty)]
    | TyArrow(t1, t2), TyArrow(t3, t4) -> compose_subst (unify t1 t3) (unify t2 t4)
    | TyTuple(tys1), TyTuple(tys2) -> List.fold2(fun acc ty1 ty2 -> let sub = unify ty1 ty2 in compose_subst acc sub) [] tys1 tys2
    | _, _ -> type_error "wrong unification: cannot unify type variable: %s and %s" (pretty_ty t1) (pretty_ty t2)


let rec new_fresh_var (env : scheme env) : ty =
    let rec max_var (max: int) (ty: ty) :tyvar =
        match ty with
        | TyVar(num) -> if num > max then num else max
        | TyTuple(nums) -> List.fold(fun max num -> let result = max_var max num in if result > max then result else max) max nums
        | TyArrow(ty1, ty2) -> let num1 = max_var max ty1 in let num2 = max_var max ty2 in if num1 > num2 then num1 else num2
        | TyName(_) -> 0
 
    TyVar(1 + List.fold(fun acc (_, (Forall(_, ty))) -> if max_var 0 ty > acc then max_var 0 ty else acc) 0 env)

let rec instantiate (Forall(type_vars, ty)) (env : scheme env) : ty =
    let new_var = new_fresh_var env
    let rec replace (oldTy:tyvar) (newTy:tyvar) (ty: ty): ty =
        match ty with
        | TyVar(num) -> if num = oldTy then TyVar(newTy) else TyVar(oldTy)
        | TyTuple(nums) -> TyTuple(List.map(fun item -> replace oldTy newTy item ) nums)
        | TyArrow(ty1, ty2) -> TyArrow(replace oldTy newTy ty1, replace oldTy newTy ty2)
        | TyName(name) -> TyName(name)
        
    match new_var with
    | TyVar(num) ->
        let _, res_ty = List.fold(fun (new_fresh, acc_ty) old_ty_var -> let new_t = replace old_ty_var new_fresh acc_ty in (new_fresh + 1, new_t)) (num, ty) type_vars
        res_ty
    | _ -> unexpected_error "it should be TyVar but got %s " (pretty_ty new_var)

let apply_subst_scheme(Forall (tvs, t)) (sub : subst) : scheme =
    Forall(tvs, apply_subst t (List.filter (fun (name, _) -> not (List.contains name tvs )) sub))

let apply_subst_to_env(env : scheme env) (sub :subst) : scheme env =
    List.map(fun (name, scheme) -> name, apply_subst_scheme scheme sub ) env


let rec freevars_ty t =
    match t with
    | TyName s -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts

let freevars_scheme (Forall (tvs, t)) = freevars_ty t - Set.ofList tvs

let freevars_scheme_env env =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

let gen_scheme_from_env (env : scheme env) (ty : ty) : scheme =
    let tvs = freevars_ty ty - freevars_scheme_env env
    Forall(Set.toList tvs, ty)

// type inference
//

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))

]

// TODO for exam
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit(LInt _) -> TyInt, []
    | Lit(LFloat _) -> TyFloat, []
    | Lit(LString _) -> TyString, []
    | Lit(LChar _) -> TyChar, []
    | Lit(LBool _) -> TyBool, []
    | Lit(LUnit _) -> TyUnit, []

    | Var(var) ->
        let _, scheme = List.find(fun (name, scheme) -> name = var ) env
        let new_ty = instantiate scheme env
        new_ty, []

    | Lambda(v, None, expr) ->
        let new_var = new_fresh_var env
        let new_schem = Forall([], new_var)
        let new_env = (v, new_schem)::env
        let t2, sub2 = typeinfer_expr new_env expr
        let final_ty = apply_subst new_var sub2
        TyArrow(final_ty, t2), sub2

    | App(exp1, exp2) ->
        let ty1, sub1 = typeinfer_expr env exp1
        let ty2, sub2 = typeinfer_expr (apply_subst_to_env env sub1) exp2
        let new_var = new_fresh_var env
        let sub3 = unify ty1 (TyArrow(ty2, new_var))
        let final_ty = apply_subst new_var sub3
        final_ty, compose_subst (compose_subst sub3 sub2) sub1

    | Let(name, ty_option, exp1, exp2) ->
        let ty1, sub1 = typeinfer_expr env exp1
        let new_env = (name, gen_scheme_from_env env ty1)::(apply_subst_to_env env sub1)
        let ty2, sub2 = typeinfer_expr new_env exp2
        let sub3 =
            match ty_option with
            | None -> []
            | Some ty -> unify ty ty2
        apply_subst ty2 sub3, compose_subst sub1 sub2

    | LetRec(name, ty_option, lambda, expr) ->
        match lambda with
        | Lambda(_) -> ()
        | something -> type_error "expecting a lambda but got %s" (pretty_expr something)

        let new_env = (name, Forall([], new_fresh_var env))::env
        let ty1, sub1 = typeinfer_expr new_env lambda
        let new_scheme = gen_scheme_from_env env ty1
        let new_env2 = (name, new_scheme)::(apply_subst_to_env env sub1)
        let ty2, sub2 = typeinfer_expr new_env2 expr

        let sub3 =
            match ty_option with
            | None -> []
            | Some ty -> unify ty ty2
        apply_subst ty2 sub3, compose_subst sub1 sub2


    | IfThenElse(expr1, expr2, expr3o) ->
        let ty1, sub1 = typeinfer_expr env expr1
        let sub2 = unify ty1 TyBool
        let sub3 = compose_subst sub2 sub1
        let ty2, sub4 = typeinfer_expr (apply_subst_to_env env sub3) expr2
        let sub5 = compose_subst sub4 sub3
        match expr3o with
        | None -> type_error "expecting a Some but got None"
        | Some expr3 ->

            let ty3, sub6 = typeinfer_expr (apply_subst_to_env env sub5) expr3
            let sub7 = compose_subst sub6 sub5
            let sub8 = unify ty2 ty3
            apply_subst ty2 sub8, compose_subst sub8 sub7

    | Tuple (exprs) ->
        let sub, tys = List.fold (fun (sub_acc, tys_acc) expr -> 
            let ty, sub = typeinfer_expr (apply_subst_to_env env sub_acc) expr  // gather subsitution
            in (compose_subst sub sub_acc, ty::tys_acc)) ([], []) exprs

        // try to have affect by applying substitution to every type in the tuple.
        // EX) fun x -> (x, if x then 1 else 3, "I love F#", x);;
        TyTuple (List.map (fun ty -> apply_subst ty sub) (List.rev tys)), sub




    | BinOp (expr1, ("<" | "<=" | ">" | ">=" | "=" | "<>"), expr2) ->
        let ty1, sub1 = typeinfer_expr env expr1
        let _ty2, _ = typeinfer_expr env expr2 
        let number_ty = 
            match ty1, _ty2 with 
            | (TyFloat, _) 
            | (_, TyFloat) -> TyFloat
            | _ -> TyInt

        let ty2, sub2 = typeinfer_expr (apply_subst_to_env env sub1) expr2

        let sub3 = unify number_ty ty1
        let sub4 = unify number_ty ty2

        TyBool, compose_subst (compose_subst (compose_subst sub4 sub3) sub2) sub1
        
    
    | BinOp (expr1, ("+" | "-" | "/" | "%" | "*"), expr2) ->
        let ty1, sub1 = typeinfer_expr env expr1
        let _ty2, _ = typeinfer_expr env expr2 
        let number_ty = 
            match ty1, _ty2 with 
            | (TyFloat, _) 
            | (_, TyFloat) -> TyFloat
            | _ -> TyInt

        let ty2, sub2 = typeinfer_expr (apply_subst_to_env env sub1) expr2

        let sub3 = unify number_ty ty1
        let sub4 = unify number_ty ty2

        number_ty, compose_subst (compose_subst (compose_subst sub4 sub3) sub2) sub1

    | BinOp (expr1, ("and" | "or"), expr2) ->
        let ty1, sub1 = typeinfer_expr env expr1
        let ty2, sub2 = typeinfer_expr (apply_subst_to_env env sub1) expr2
        let sub3 = unify TyBool ty1
        let sub4 = unify TyBool ty2

        TyBool, compose_subst (compose_subst (compose_subst sub4 sub3) sub2) sub1

    | UnOp ("-", expr1) ->
        let ty1, sub1 = typeinfer_expr env expr1
        let number_ty = 
            match ty1 with 
            | TyFloat -> TyFloat
            | _ -> TyInt
        let sub2 = unify number_ty ty1
        number_ty, compose_subst sub2 sub1

    | UnOp ("not", expr1) ->
        let ty1, sub1 = typeinfer_expr env expr1
        let sub2 = unify TyBool ty1
        TyBool, compose_subst sub2 sub1


    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

        
        


// type checker
//
    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
