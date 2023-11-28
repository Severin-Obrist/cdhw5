open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  begin match t1, t2 with
  | TInt, TInt                    -> true
  | TBool, TBool                  -> true
  | TRef rty1, TRef rty2          -> subtype_ref c rty1 rty2
  | TRef rty1, TNullRef rty2      -> subtype_ref c rty1 rty2
  | TNullRef rty1, TNullRef rty2  -> subtype_ref c rty1 rty2
  | _                             -> false
  end


(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  begin match t1, t2 with
  | RString, RString          -> true
  | RArray a1, RArray a2      -> (a1 = a2)
  | RStruct id1, RStruct id2  -> subtype_struct c id1 id2
  | RFun(args1, ret1), RFun(args2, ret2) -> 
    subtype_ret_ty c ret1 ret2 && (subtype_args c args2 args1)
  | _                         -> false
  end

and subtype_args c ls1 ls2 = 
  begin match ls1, ls2 with
    | a::tl, a'::tl' -> (subtype c a a') && (subtype_args c tl tl') 
    | [],[] -> true
    | _,_ -> false
  end

and subtype_struct c id1 id2 =
  let flsopt1 = lookup_struct_option id1 c and flsopt2  = lookup_struct_option id2 c in
  let is_subtype =  begin match flsopt1, flsopt2 with
                    | Some ls1, Some ls2  -> begin match ls1, ls2 with
                                              | _, [] -> true
                                              | [], _ -> false
                                              | _     -> List.fold_left (fun b x -> b && (List.mem x ls1)) true ls2
                                             end
                    | _, None | None, _ | None, None -> false
                    end in
  is_subtype

and subtype_ret_ty c ret1 ret2 = 
  begin match ret1, ret2 with
  | RetVal t1, RetVal t2  -> subtype c t1 t2
  | RetVoid, RetVoid      -> true
  | _                     -> false
  end

  

(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is not well-formed

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  begin match t with
  | TInt          -> ()
  | TBool         -> ()
  | TRef rty      -> typecheck_ref l tc rty
  | TNullRef rty  -> typecheck_ref l tc rty
  | _             -> type_error l "Bad type"
  end

and typecheck_ref l tc rty =
  begin match rty with
  | RString               -> ()
  | RArray a1             -> typecheck_ty l tc a1
  | RStruct id1           -> if lookup_struct_option id1 tc == None then type_error l "None Struct" else ()
  | RFun (tyls1, retty1)  -> if (List.fold_left (fun b x -> b &&  (Unit.equal (typecheck_ty l tc x) ())) (Unit.equal (typecheck_retty l tc retty1) ()) tyls1) then () else type_error l "Bad Function"
  | _                     -> type_error l "Bad reference type"
  end

and typecheck_retty l tc retty = 
  begin match retty with
  | RetVoid   -> ()
  | RetVal ty -> typecheck_ty l tc ty
  | _         -> type_error l "Bad return type"
  end

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec print_ctxt c = 
  match c with
  | l::ls -> print_endline (fst l); print_ctxt ls
  | [] -> ()

let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  begin match e.elt with
    | CNull rty -> typecheck_ref e c (rty); TNullRef rty
    | CBool _ -> TBool
    | CInt _ -> TInt
    | CStr _ -> TRef RString
    | Id id ->  let id_ty = lookup_local_option id c in 
                begin match id_ty with
                  | Some ty   -> ty
                  | None      ->  let gid_ty = lookup_global_option id c in
                                  begin match gid_ty with
                                    | Some gy -> gy
                                    | None -> type_error e @@ "Bad ID: " ^ id
                                  end
                end
    | CArr (ty, exp_ls) ->  (typecheck_ty e c ty);
                            let ty_ls = List.fold_left (fun ls x -> ls@[typecheck_exp c x]) [] exp_ls in
                            let is_subtype = List.fold_left (fun b x -> b && subtype c x ty) true ty_ls in 
                            if is_subtype then (TRef (RArray ty)) else type_error e "Bad CArr"
    | NewArr (ty, exp1_n, id, exp2_n) ->  (typecheck_ty e c ty);
                                          if (typecheck_exp c exp1_n) == TInt then () else type_error e "Bad NewArr";
                                          let t' =  begin match lookup_local_option id c with
                                                    | Some _ -> type_error e "Bad NewArr"
                                                    | None -> typecheck_exp (add_local c id TInt) exp2_n
                                                    end in 
                                          if subtype c t' ty then TRef (RArray ty) else type_error e "Bad NewArr";
    | Index (exp1_n, exp2_n) -> begin match typecheck_exp c exp1_n with
                                | TRef (RArray ty)  -> 
                                              begin match typecheck_exp c exp2_n with
                                              | TInt -> ty
                                              | _ -> type_error e "Bad Index"
                                              end
                                | _ -> type_error e "Not an array"
                                end
    | Length exp1_n ->  begin match typecheck_exp c exp1_n with
                        | TRef (RArray _) -> TInt;
                        | _ -> type_error e "exp1 is not an array"
                        end
    | CStruct (id, exp_ls) -> let sorted_fields_ls =  begin match lookup_struct_option id c with
                                        | Some s -> List.sort (fun field1 field2 -> if field1.fieldName == field2.fieldName then 0 else if field1.fieldName < field2.fieldName then -1 else 1) s
                                        | None -> type_error e "Struct not in context (typecheck exp)"
                                        end in
                          let idty_ls = List.fold_left (fun ls (id,x) -> ls@[(id,typecheck_exp c x)]) [] exp_ls in
                          let sorted_idty_ls = List.sort (fun (a,b) (c,d) -> if a == c then 0 else if a < c then -1 else 1) idty_ls in
                          if List.length sorted_fields_ls <> List.length sorted_idty_ls then type_error e "struct field length mismatch" else ();
                          if (List.fold_left (fun bol ((a,b), field) -> bol && subtype c b field.ftyp) true (List.combine sorted_idty_ls sorted_fields_ls)) then TRef (RStruct id) else type_error e "Bad Struct"
    | Proj (expn_1, fid) -> let exp1_ty = typecheck_exp c expn_1 in 
                            begin match exp1_ty with
                            | TRef (RStruct id) -> begin match lookup_field_option id fid c with
                                                    | Some field -> field
                                                    | None -> type_error expn_1 "field not found in struct"
                                                  end
                            | _ -> type_error e "Bad Struct (Field)"
                            end
    | Call (exp1_n, exp_ls) ->  begin match typecheck_exp c exp1_n with
                                | TRef (RFun (tyls1, retty1)) ->  let ty_ls = List.fold_left (fun ls x -> ls@[typecheck_exp c x]) [] exp_ls in
                                                                  if List.length ty_ls <> List.length tyls1 then type_error exp1_n "argument length mismatch" else ();
                                                                  let is_subtype = List.fold_left (fun b (x,y) -> b && subtype c x y ) true (List.combine ty_ls tyls1) in
                                                                  if is_subtype then begin match retty1 with
                                                                                      | RetVoid   -> type_error e "can't use a void function in an expression" (*maybe wrong and TODO*)
                                                                                      | RetVal ty -> ty
                                                                                      | _         ->  type_error e "Bad return type in Call typecheck"
                                                                                      end
                                                                                    else type_error e "Bad Call"
                                | _ -> type_error e "call - not a functino"
                                end
    | Bop (Eq, exp1_n, exp2_n)    ->  let t1' = typecheck_exp c exp1_n and t2' = typecheck_exp c exp2_n in
                                      if(subtype c t1' t2') && (subtype c t2' t1') then TBool else  type_error e "Bad Eq Bop"
    | Bop (Neq, exp1_n, exp2_n)   ->  let t1' = typecheck_exp c exp1_n and t2' = typecheck_exp c exp2_n in
                                      if(subtype c t1' t2') && (subtype c t2' t1') then TBool else  type_error e "Bad Neq Bop"
    | Bop (bop, exp1_n, exp2_n) -> let t1, t2, retty = typ_of_binop bop in
                                   if (typecheck_exp c exp1_n == t1) && (typecheck_exp c exp2_n == t2) then retty else type_error e "Bad Bop"
    | Uop (uop, exp1_n) ->  let t1, retty = typ_of_unop uop in
                            if (typecheck_exp c exp1_n == t1) then retty else type_error e "Bad Uop"
                                
    | _  -> type_error e "Bad Exp"
  end

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statement typechecking rules from oat.pdf.  

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement
     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, both branches must definitely return

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entier conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)


let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  match s.elt with
  | Assn (exp1_n, exp2_n)                     ->  let _ = begin match exp1_n.elt with
                                                               | Id i -> begin match lookup_option i tc with
                                                                          | Some TRef (RFun _) -> begin match lookup_global_option i tc with
                                                                                                    | Some _ -> type_error exp1_n "cant assign values to functions"
                                                                                                    | None -> ()
                                                                                                  end
                                                                          | Some _ -> ()
                                                                          | None   -> type_error exp1_n "variable not in context"
                                                                          end;
                                                               | Index _ | Proj _ -> ()
                                                               | _ -> type_error exp1_n "unknown lhs, can't assign"
                                                          end in                                                  
                                                  let lhs_t = typecheck_exp tc exp1_n and rhs_t = typecheck_exp tc exp2_n in
                                                  if subtype tc rhs_t lhs_t then (tc, false) else type_error exp1_n "LHS not supertype of RHS"
  | Decl (vd_id, vd_exp_n)                    ->  let exp_ty = typecheck_exp tc vd_exp_n in
                                                  begin match lookup_local_option vd_id tc with
                                                  | Some _ -> type_error vd_exp_n "declared variable alraedy in context"
                                                  | None -> begin match lookup_struct_option vd_id tc with
                                                              | Some _ -> type_error vd_exp_n "declared variable alraedy in context"
                                                              | None -> (add_local tc vd_id exp_ty, false)
                                                            end
                                                  end
  | Ret (Some exp_n)                          ->  let t' = typecheck_exp tc exp_n in
                                                  begin match to_ret with
                                                  | RetVoid   -> type_error exp_n "expected void return but got something else"
                                                  | RetVal t  -> if subtype tc t' t then (tc, true) else type_error exp_n "return type is not subtype of expected return type"
                                                  end
  | Ret None                                  ->  begin match to_ret with
                                                  | RetVoid   -> (tc, true)
                                                  | RetVal t  -> type_error s "expect non void return but got void"
                                                  end
  | SCall (exp_n, exp_ls)                     ->  let super_ty_ls = begin match typecheck_exp tc exp_n with
                                                  | TRef (RFun(a, RetVoid)) -> a
                                                  | _ -> type_error exp_n "expression not void"
                                                  end in
                                                  let sub_ty_ls = List.fold_left(fun ty_ls exp ->
                                                    ty_ls@[typecheck_exp tc exp]
                                                    ) [] exp_ls in
                                                  if List.length super_ty_ls <> List.length sub_ty_ls then type_error exp_n "argument length mismatch" else ();
                                                  let is_all_subtype = List.fold_left(fun b (sub, sup) -> b && (subtype tc sub sup)) true (List.combine sub_ty_ls super_ty_ls) in (* TODO if error, check rule again precisely *)
                                                  if is_all_subtype then (tc, false) else type_error exp_n "Params have wrong type"
  | If (exp_n, stm1_ls, stm2_ls)              ->  let guard_ty = typecheck_exp tc exp_n in
                                                  begin match guard_ty with
                                                    | TBool         ->  let (_, true_block_returns) = typecheck_block tc stm1_ls to_ret and (_, false_block_returns) = typecheck_block tc stm2_ls to_ret in
                                                                tc, (true_block_returns && false_block_returns)
                                                    | _     -> type_error exp_n "If - expression doesn't return a bool"
                                                  end
  | Cast (refty, id, exp_n, stm1_ls, stm2_ls) ->  let t_ref = begin match typecheck_exp tc exp_n with
                                                    | TNullRef t -> TRef t
                                                    | _          -> type_error exp_n "cant cast to a non-null-reference"
                                                  end in
                                                  begin match subtype tc t_ref (TRef refty) with
                                                    | false -> type_error exp_n "casting types are not subtypes"
                                                    | true  ->  let tc' = add_local tc id t_ref in
                                                                let _, bl1 = typecheck_block tc' stm1_ls to_ret and _, bl2 = typecheck_block tc' stm2_ls to_ret in
                                                                tc, bl1 && bl2
                                                  end
  | For (vd_ls, exp_n_o, stm_n_o, stm_ls)     ->  let tc' = List.fold_left (fun c (id, exp) -> 
                                                    let exp_ty = typecheck_exp c exp in
                                                    begin match lookup_option id c with
                                                      | Some _ -> type_error s "For-variable already in context"
                                                      | None -> Tctxt.add_local c id exp_ty
                                                    end) tc vd_ls in
                                                  let exp_n = begin match exp_n_o with
                                                      | Some exp -> exp
                                                      | None -> type_error s "For - empty expression not supported"
                                                    end in
                                                  let stmt_n = begin match stm_n_o with
                                                      | Some stmt -> stmt
                                                      | None -> type_error s "For - empty statement not supported"
                                                    end in
                                                  let _, for_stmt_returns = typecheck_stmt tc' stmt_n to_ret in
                                                  if for_stmt_returns then type_error stmt_n "For - Statement isn't allowed to return" else ();
                                                  let guard_ty = typecheck_exp tc' exp_n in
                                                    begin match guard_ty with
                                                      | TBool ->  let _ = typecheck_block tc' stm_ls to_ret in
                                                                  tc, false
                                                      | _     -> type_error exp_n "while - expression doesn't return a bool"
                                                    end
  | While (exp_n, stm_ls)                     -> let guard_ty = typecheck_exp tc exp_n in
                                                  begin match guard_ty with
                                                    | TBool ->  let _ = typecheck_block tc stm_ls to_ret in
                                                                tc, false
                                                    | _     -> type_error exp_n "while - expression doesn't return a bool"
                                                  end
  | _                                         -> failwith "not a valid statement"

  and typecheck_block (tc : Tctxt.t) (sl:Ast.stmt node list) (to_ret:ret_ty) : Tctxt.t * bool = 
      let returns, tc' = List.fold_left (fun (b, c) s -> 
        let stmt_c, stmt_b = typecheck_stmt c s to_ret in
        begin if b then
          type_error s "block returns before last statement"
        else
          (b || stmt_b), stmt_c end) (false, tc) sl in
      tc', returns


(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | []      -> false
  | h :: t  -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)
let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let rev_args = List.fold_left (fun ls (a,b) -> (b,a)::ls) [] f.args in
  let tc = {locals=rev_args@tc.locals; globals=tc.globals; structs=tc.structs} in
  let _, returns = typecheck_block tc f.body f.frtyp in
  if returns then () else type_error l "function doesnt return"
  

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  begin match p with
  | []    -> Tctxt.empty
  | d_ls  -> List.fold_left (fun c x -> begin match x with
                                        | Gvdecl gd -> c
                                        | Gfdecl fd -> c
                                        | Gtdecl td ->  begin match lookup_struct_option (fst td.elt) c with
                                                        | Some _  -> type_error td "struct already in context"
                                                        | None    -> add_struct c (fst td.elt) (snd td.elt)
                                                        end
                                        | _         -> failwith "not a decl (create_struct_ctxt)"
                                        end
                            ) Tctxt.empty d_ls
  | _     -> failwith "Not a program"
  end

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let tc' = List.fold_left (fun c (id, (arg, ret)) -> Tctxt.add_global c id (TRef(RFun(arg,ret)))) tc builtins in
  begin match p with
  | []    -> tc'
  | d_ls  -> List.fold_left (fun c x -> begin match x with
                                        | Gvdecl gd -> c
                                        | Gfdecl fd ->  let retty = fd.elt.frtyp in
                                                        let fid = fd.elt.fname in
                                                        let (ty_ls, _) = List.split fd.elt.args in
                                                        begin match lookup_global_option fid c with
                                                        | Some _  -> type_error fd "function already in context"
                                                        | None    -> add_global c fid (TRef(RFun (ty_ls, retty)))
                                                        end
                                        | Gtdecl td -> c
                                        | _         -> failwith "not a decl (create_struct_ctxt)"
                                        end
                            ) tc' d_ls
  | _   -> failwith "Not a program"
  end


(* helper function to check wether gexp conains any globals*)
let rec contains_globals funct_c glob_c gexp =
  begin match gexp with
  | CNull _ | CInt _ | CBool _ | CStr _ -> false
  | CArr (_, exp_ls) | Call (_, exp_ls) -> List.fold_left (fun b exp -> b || contains_globals funct_c glob_c exp.elt) false exp_ls
  | NewArr (_, exp1_n, _, exp2_n) | Index (exp1_n, exp2_n) | Bop (_, exp1_n, exp2_n) -> (contains_globals funct_c glob_c exp1_n.elt) || (contains_globals funct_c glob_c exp2_n.elt)
  | Length exp_n | Uop (_, exp_n) | Proj (exp_n, _) -> contains_globals funct_c glob_c exp_n.elt
  | CStruct (_, id_exp_ls) -> List.fold_left (fun b (_, exp) -> b || contains_globals funct_c glob_c exp.elt) false id_exp_ls
  | Id i -> begin match lookup_global_option i funct_c with
            | Some _ -> false
            | None -> begin match lookup_global_option i glob_c with
                      | Some _ -> true
                      | None -> false
                      end
            end
  end

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  begin match p with
  | []    -> tc
  | d_ls  -> List.fold_left (fun tc' decl -> 
              begin match decl with
                | Gvdecl gd -> 
                  let gexp_ty = typecheck_exp tc' gd.elt.init in
                  if contains_globals tc tc' gd.elt.init.elt then type_error gd "global declaration contains other globals"
                  else ();
                  begin match lookup_global_option gd.elt.name tc'  with
                    | Some _ -> type_error gd "global declaration is already in context"
                    | None   -> add_global tc' gd.elt.name gexp_ty
                  end
                | _ -> tc'
              end) tc d_ls
  | _   -> failwith "Not a program"
  end

(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p
