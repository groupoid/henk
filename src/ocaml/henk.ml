(* Henk: CoC 1988 with infinite hierarchy of impredicative universes *)

type universe = int

type term =
  | Var of string
  | Universe of universe
  | Pi of string * term * term      (* ∀ (x : a), b *)
  | Lambda of string * term * term  (* λ (x : a), b *)
  | App of term * term

type context = (string * term) list

let rec string_of_term = function
  | Var x -> x
  | Universe u -> "U_" ^ string_of_int u
  | Pi (x, a, b) -> "∀ (" ^ x ^ " : " ^ string_of_term a ^ "), " ^ string_of_term b
  | Lambda (x, a, t) -> "λ (" ^ x ^ " : " ^ string_of_term a ^ "), " ^ string_of_term t
  | App (t1, t2) -> "(" ^ string_of_term t1 ^ " " ^ string_of_term t2 ^ ")"

let fresh_var used_vars base =
  let rec find_fresh n =
    let candidate = base ^ string_of_int n in
    if List.mem candidate used_vars then find_fresh (n + 1) else candidate
  in find_fresh 0

let rec free_vars = function
  | Var x -> [x]
  | Universe _ -> []
  | Pi (x, a, b) -> free_vars a @ List.filter ((<>) x) (free_vars b)
  | Lambda (x, a, t) -> free_vars a @ List.filter ((<>) x) (free_vars t)
  | App (t1, t2) -> free_vars t1 @ free_vars t2

let rec subst x arg body =
  match body with
  | Var y -> if y = x then arg else body
  | Universe u -> Universe u
  | Pi (y, a, b) ->
      if y = x then Pi (y, subst x arg a, b)
      else
        let fv = free_vars arg in
        if List.mem y fv then
          let y' = fresh_var (fv @ free_vars a @ free_vars b) y in
          let b' = subst y (Var y') b in
          Pi (y', subst x arg a, subst x arg b')
        else Pi (y, subst x arg a, subst x arg b)
  | Lambda (y, a, t) ->
      if y = x then Lambda (y, subst x arg a, t)
      else
        let fv = free_vars arg in
        if List.mem y fv then
          let y' = fresh_var (fv @ free_vars a @ free_vars t) y in
          let t' = subst y (Var y') t in
          Lambda (y', subst x arg a, subst x arg t')
        else Lambda (y, subst x arg a, subst x arg t)
  | App (t1, t2) -> App (subst x arg t1, subst x arg t2)

let rec normalize = function
  | Var x -> Var x
  | Universe u -> Universe u
  | Pi (x, a, b) -> Pi (x, normalize a, normalize b)
  | Lambda (x, a, t) -> Lambda (x, normalize a, normalize t)
  | App (t1, t2) ->
      let t1' = normalize t1 in
      let t2' = normalize t2 in
      match t1' with
      | Lambda (x, _, body) -> normalize (subst x t2' body)  (* Beta reduction *)
      | _ -> App (t1', t2')

let eta_expand t typ =
  match typ with
  | Pi (x, a, b) ->
      let x' = fresh_var (free_vars t) x in
      Lambda (x', a, App (t, Var x'))
  | _ -> t

let rec equal_terms t1 t2 =
  let t1' = normalize t1 in
  let t2' = normalize t2 in
  match t1', t2' with
  | Var x, Var y -> x = y
  | Universe u1, Universe u2 -> u1 = u2
  | Pi (x1, a1, b1), Pi (x2, a2, b2) ->
      equal_terms a1 a2 && equal_terms (subst x1 (Var x2) b1) b2
  | Lambda (x1, a1, t1'), Lambda (x2, a2, t2') ->
      equal_terms a1 a2 && equal_terms (subst x1 (Var x2) t1') t2'
  | App (t1a, t1b), App (t2a, t2b) ->
      equal_terms t1a t2a && equal_terms t1b t2b
  | _ ->
      (* Check eta equality: f = λx. (f x) *)
      let try_eta t t' =
        match t' with
        | Lambda (x, a, App (f, Var y)) when y = x && not (List.mem x (free_vars f)) ->
            equal_terms t f
        | _ -> false
      in
      try_eta t1' t2' || try_eta t2' t1'

let rec infer_type ctx = function
  | Var x -> lookup_var ctx x
  | Universe u -> Universe (u + 1)
  | Pi (x, a, b) ->
      let a_type = infer_type ctx a in
      (match a_type with
       | Universe i ->
           let b_type = infer_type ((x, a) :: ctx) b in
           (match b_type with
            | Universe j -> Universe (max i j)
            | _ -> failwith "Pi body must be a type")
       | _ -> failwith "Pi domain must be a type")
  | Lambda (x, a, body) ->
      let a_type = infer_type ctx a in
      (match a_type with
       | Universe _ ->  (* Ensure 'a' is a valid Universe *)
           let body_type = infer_type ((x, a) :: ctx) body in
           Pi (x, a, body_type)
       | _ -> failwith "Lambda annotation must be a type")
  | App (t1, t2) ->
      let t1_type = normalize (infer_type ctx t1) in
      (match t1_type with
       | Pi (x, a, b) ->
           let t2_type = normalize (infer_type ctx t2) in
           if equal_terms t2_type a then subst x t2 b
           else failwith ("Universe mismatch: expected " ^ string_of_term a ^ ", got " ^ string_of_term t2_type)
       | _ -> failwith "Application requires a Pi type")

and lookup_var ctx x =
  match ctx with
  | [] -> failwith ("Unbound variable: " ^ x)
  | (y, typ) :: rest -> if x = y then typ else lookup_var rest x

(* Test Suite *)

let nat_type =
    Pi ("Nat", Universe 0,
    Pi ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Pi ("Zero", Var "Nat", Var "Nat")))

let zero =
    Lambda ("Nat", Universe 0,
    Lambda ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lambda ("Zero", Var "Nat", Var "Zero")))

let succ =
    Lambda ("pred", nat_type,
    Lambda ("Nat", Universe 0,
    Lambda ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lambda ("Zero", Var "Nat",
    App (Var "Succ", App (App (App (Var "pred", Var "Nat"), Var "Succ"), Var "Zero"))))))


let list_type =
    Pi ("List", Universe 0,
    Pi ("Cons", Pi ("head", nat_type, Pi ("tail", Var "List", Var "List")),
    Pi ("Nil", Var "List", Var "List")))

let beta_test = let lam = Lambda ("x", Universe 0, Var "x") in let app = App (lam, Var "y") in (app, Var "y")
let eta_test ctx f f_type = let eta_expanded = eta_expand f f_type in (f, eta_expanded)

let run_type_test name term expected_type =
  let ctx = [] in
  try
    let inferred = infer_type ctx term in
    let norm_inferred = normalize inferred in
    let norm_expected = normalize expected_type in
    Printf.printf "Test %s:\n- Term: %s\n- Inferred: %s\n- Expected: %s\n- Result: %s\n\n"
      name
      (string_of_term term)
      (string_of_term norm_inferred)
      (string_of_term norm_expected)
      (if equal_terms norm_inferred norm_expected then "PASS" else "FAIL")
  with
  | Failure msg -> Printf.printf "Universe Test %s: Failed with error: %s\n\n" name msg

let run_equality_test name (t1, t2) =
  let result = equal_terms t1 t2 in
  Printf.printf "Equality Test %s:\n- Term1: %s\n- Term2: %s\n- Result: %s\n\n"
    name
    (string_of_term t1)
    (string_of_term t2)
    (if result then "PASS" else "FAIL")

let () =
  (* Nat tests *)
  run_type_test "Nat" nat_type (Universe 1);
  run_type_test "Zero" zero nat_type;
  run_type_test "Succ" succ (Pi ("pred", nat_type, nat_type));
  (* Beta equality test *)
  run_equality_test "Beta" beta_test; 
  (* Eta equality test *)
  let ctx = [("s", succ, infer_type [] succ)] in
  let f_type = infer_type [] succ in
  run_equality_test "Eta (Succ)" (eta_test ctx (Var "s") f_type)
