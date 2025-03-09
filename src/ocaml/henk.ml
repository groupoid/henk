(* Henk: CoC 1988 with infinite hierarchy of predicative universes *)

type term =
  | Var of string
  | Universe of int
  | Pi of string * term * term   (* ∀ (x : a), b *)
  | Lam of string * term * term  (* λ (x : a), b *)
  | App of term * term

type context = (string * term) list

exception TypeError of string

let subst x s t = let rec subst_many m t =
    match t with
    | Var x -> (try List.assoc x m with Not_found -> t)
    | Pi (x, a, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Pi (x, subst_many m a, subst_many m' b)
    | Lam (x, d, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Lam (x, subst_many m d, subst_many m' b)
    | App (f, arg) -> App (subst_many m f, subst_many m arg)
    | _ -> t in subst_many [(x, s)] t

let rec lookup_var ctx x =
    match ctx with
    | [] -> failwith ("Unbound variable: " ^ x)
    | (y, typ) :: rest -> if x = y then typ else lookup_var rest x

let rec string_of_term = function
    | Var x -> x
    | Universe u -> "U_" ^ string_of_int u
    | Pi (x, a, b) -> "∀ (" ^ x ^ " : " ^ string_of_term a ^ "), " ^ string_of_term b
    | Lam (x, a, t) -> "λ (" ^ x ^ " : " ^ string_of_term a ^ "), " ^ string_of_term t
    | App (t1, t2) -> "(" ^ string_of_term t1 ^ " " ^ string_of_term t2 ^ ")"

let check_universe ty =
    match ty with
    | Universe i -> if i < 0 then raise (TypeError "Negative universe level"); i
    | ty -> raise (TypeError (Printf.sprintf "Expected a universe, got: %s" (string_of_term ty)))

let rec equal' ctx t1 t2 =
    match t1, t2 with
    | Var x, Var y -> x = y
    | Universe i, Universe j -> i <= j
    | Pi (x, a, b), Pi (y, a', b') -> equal' ctx a a' && equal' ((x,a) :: ctx) b (subst y (Var x) b')
    | Lam (x, d, b), Lam (y, d', b') -> equal' ctx d d' && equal' ((x,d) :: ctx) b (subst y (Var x) b')
    | Lam (x, d, b), t -> equal' ctx b (App (t, Var x))
    | t, Lam (x, d, b) -> equal' ctx (App (t, Var x)) b
    | App (f, arg), App (f', arg') -> equal' ctx f f' && equal' ctx arg arg'
    | _ -> t1 = t2

let rec equal ctx t1 t2 =
    let t1' = normalize ctx t1 in
    let t2' = normalize ctx t2 in
    match t1', t2' with
    | Lam (x, d, b), t -> (match infer ctx t1' with | Pi _ -> equal' ctx t1' t2' | _ -> false)
    | t, Lam (x, d, b) -> (match infer ctx t2' with | Pi _ -> equal' ctx t1' t2' | _ -> false)
    | _ -> equal' ctx t1' t2'

and reduce ctx t =
    match t with
    | App (Lam (x, domain, body), arg) -> subst x arg body
    | App (Pi (x, a, b), arg) -> subst x arg b
    | App (f, arg) -> let f' = reduce ctx f in let arg' = reduce ctx arg in App (f', arg')
    | _ -> t

and normalize ctx t =
    let t' = reduce ctx t in
    if equal' ctx t t' then t else normalize ctx t'

and infer ctx t =
    let res = match t with
    | Var x -> lookup_var ctx x
    | Universe i -> if i < 0 then raise (TypeError "Negative universe level"); Universe (i + 1)
    | Pi (x, a, b) -> let i = check_universe (infer ctx a) in let ctx' = (x,a)::ctx in let j = check_universe (infer ctx' b) in Universe (max i j)
    | Lam (x, domain, body) -> let _ = infer ctx domain in let body_ty = infer ((x,domain)::ctx) body in Pi (x, domain, body_ty)
    | App (f, arg) -> match infer ctx f with | Pi (x, a, b) -> subst x arg b | ty -> raise (TypeError "Application requires a Pi type.")
    in normalize ctx res

(* Test Suite *)

let nat_type =
    Pi ("Nat", Universe 0,
    Pi ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Pi ("Zero", Var "Nat", Var "Nat")))

let zero =
    Lam ("Nat", Universe 0,
    Lam ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lam ("Zero", Var "Nat", Var "Zero")))

let succ =
    Lam ("pred", nat_type,
    Lam ("Nat", Universe 0,
    Lam ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lam ("Zero", Var "Nat",
    App (Var "Succ", App (App (App (Var "pred", Var "Nat"), Var "Succ"), Var "Zero"))))))

let list_type =
    Pi ("List", Universe 0,
    Pi ("Cons", Pi ("head", nat_type, Pi ("tail", Var "List", Var "List")),
    Pi ("Nil", Var "List", Var "List")))

let sum =
    Lam ("xs", list_type,
    App (App (App (Var "xs", nat_type),
    Lam ("head", nat_type,
    Lam ("tail", nat_type,
    Lam ("Nat", Universe 0,
    Lam ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lam ("Zero", Var "Nat",
    App (App (App (Var "head", Var "Nat"), App (App (Var "tail", Var "Nat"), Var "Succ")),
    Var "Zero"))))))), zero))

let one =
    Lam ("Nat", Universe 0,
    Lam ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lam ("Zero", Var "Nat",
    App (Var "Succ", Var "Zero"))))

let two =
    Lam ("Nat", Universe 0,
    Lam ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lam ("Zero", Var "Nat",
    App (Var "Succ",
    App (Var "Succ", Var "Zero")))))

let nil =
    Lam ("List", Universe 1,
    Lam ("Cons", Pi ("head", nat_type, Pi ("tail", Var "List", Var "List")),
    Lam ("Nil", Var "List",
    Var "Nil")))

let cons head tail =
    Lam ("List", Universe 1,
    Lam ("Cons", Pi ("head", nat_type, Pi ("tail", Var "List", Var "List")),
    Lam ("Nil", Var "List", App (App (Var "Cons", head), tail))))

let list_one_two = cons one (cons two nil)

let run_type_test name term expected_type =
    let ctx = [] in
    try let inferred = infer ctx term in
        let norm_inferred = normalize ctx inferred in
        let norm_expected = normalize ctx expected_type in
        Printf.printf "Test %s:\n- Term: %s\n- Inferred: %s\n- Expected: %s\n- Result: %s\n\n"
          name
          (string_of_term term)
          (string_of_term norm_inferred)
          (string_of_term norm_expected)
          (if equal [] norm_inferred norm_expected then "PASS" else "FAIL")
    with | Failure msg -> Printf.printf "Universe Test %s: Failed with error: %s\n\n" name msg

let run_equality_test ctx name (t1, t2) =
    let result = equal ctx t1 t2 in
    Printf.printf "Equality Test %s:\n- Term1: %s\n- Term2: %s\n- Result: %s\n\n"
      name
      (string_of_term t1)
      (string_of_term t2)
      (if result then "PASS" else "FAIL")


let beta           = (App (Lam ("x", Universe 0, Var "x"), Var "y"), Var "y")
let eta            = (Lam ("x", Universe 0, App (Var "f", Var "x")), Var "f")
let eta_domain     = (Lam ("x", Universe 1, App (Var "f", Var "x")), Var "f")
let invalid_eta    = (Lam ("x", Universe 0, Universe 0), Universe 0)
let invalid_eta_v  = (Lam ("x", Universe 0, Var "u"), Var "u")
let eta_subtle     = (Lam ("x", Universe 0, Var "u"), Var "u")
let tricky_eta     = (Lam ("x", Universe 0, App (Var "f", Var "u")), Var "u")
let invalid_tricky = (Lam ("x", Universe 0, App (Var "id", Var "u")), Var "u")
let multi_beta     = (App (App (Lam ("x", Universe 0, Lam ("y", Universe 0, Var "x")), Var "u"), Var "y"), Var "u")
let predicative    = Pi ("x", Universe 0, Universe 0)
let neutral_eta    = (Lam ("x", Universe 0, App (Var "f", Var "u")), App (Var "f", Var "u"))

let () =
    let ctx = [("s", succ);("f", Pi ("x", Universe 0, Universe 0)); ("u", Universe 0); ("y", Universe 0); ("id", Pi ("x", Universe 0, Var "x"))] in
    run_type_test "Nat" nat_type (Universe 1);
    run_type_test "Zero" zero nat_type;
    run_type_test "Succ" succ (Pi ("pred", nat_type, nat_type));
    run_type_test "Sum" sum (Pi ("xs", list_type, nat_type));
    run_equality_test ctx "Beta" beta;
    run_equality_test ctx "Eta" eta;
    run_equality_test ctx "Invalid Eta" invalid_eta;
    run_equality_test ctx "Invalid Eta Var" invalid_eta_v;
    run_equality_test ctx "Tricky Eta" tricky_eta;
    run_equality_test ctx "Invalid Tricky Eta" invalid_tricky;
    run_equality_test ctx "Multi Beta" multi_beta;
    run_equality_test ctx "Eta Domain" eta_domain;
    run_type_test "CoC with Predicative Hierarchy" predicative (Universe 1);
    run_equality_test ctx "Neutral Eta" neutral_eta;
