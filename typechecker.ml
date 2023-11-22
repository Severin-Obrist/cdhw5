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
  | RArray a1, RArray a2      -> (a1 == a2)
  | RStruct id1, RStruct id2  -> subtype_struct c id1 id2
  | _                         -> false
  end

and subtype_struct c id1 id2 =
  let flsopt1 = lookup_struct_option id1 c and flsopt2  = lookup_struct_option id2 c in
  let fls1, fls2 =  begin match flsopt1, flsopt2 with
                    | Some ls1, Some ls2  -> ls1, ls2
                    | Some ls1, None      -> ls1, []
                    | None, Some ls2      -> [], ls2
                    | None, None          -> [], []
                    end in
  List.fold_left (fun b x -> b && (List.mem x fls1)) true fls2
  

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
                                    | None -> type_error e "Bad ID"
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
  failwith "todo: implement typecheck_stmt"


(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

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
  failwith "todo: typecheck_fdecl"

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
  failwith "todo: create_struct_ctxt"

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  failwith "todo: create_function_ctxt"

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  failwith "todo: create_function_ctxt"


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
