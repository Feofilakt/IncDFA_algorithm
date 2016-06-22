open System

type DFA = { Σ : Set<char>;
             Q : Set<int>;
             q0 : int;
             F : Set<int>;
             δ : Map<int * char, int> }
             //with member this. = (this.Name, x.Age)

//type DFA(Σ : Set<char>,
//         Q : Set<int>,
//         q0 : int,
//         F : Set<int>,
//         δ : Map<int * char, int>) =
//         
//    ///Alphabet that is set of symbols
//    member this.Σ = Σ
//    
//    ///States that are marked by int numbers
//    member this.Q = Q
//    
//    ///Initial state from Q
//    member this.q0 = q0
//    
//    ///Final states from Q
//    member this.F = F
//    
//    ///Transitions that are mapping between pairs (state, symbol) and states
//    //member this.Transitions = transitions
//    member this.δ = δ
    
    ///<summary> Partial mapping </summary>
    ///<param name="q"> State to start from </param>
    ///<param name="a"> Input symbol </param>
    ///<returns> Some state if mapping exists or None in other case </returns>
    //member this.δ q a =
        //this.Transitions.TryFind (q, a)
//        Option.bind (fun q -> this.Transitions.TryFind (q, a)) q
    
    ///<summary> Extended mapping </summary>
    ///<param name="q"> State to start from </param>
    ///<param name="ω"> Input string </param>
    ///<returns> Some state if mapping exists or None in other case </returns>
//    member this.δ' q ω =
//        match ω with
//        | [] -> (Some q)
//        | a :: x ->
//            this.δ q a
//            |> Option.bind (fun q_next -> this.δ' q_next x)
    
    ///<summary> Trying to accept the input string </summary>
    ///<param name="ω"> Input string </param>
    ///<returns> True if ω is accepted by automaton or False in other case </returns>
//    member this.Accept ω =
//        this.δ' q0 ω
//        |> Option.fold (fun _ q -> F.Contains q) false
        
///
//let addState q (mappings : List<char*int>) isFinal (M : DFA) =
//    DFA(M.Σ,
//        M.Q.Add q,
//        M.q0,
//        (if isFinal then M.F.Add q else M.F),
//        (List.fold (fun δ (a, q_next) -> Map.add (q, a) q_next δ) M.δ mappings))
//let addState q mappings isFinal (M : DFA) =
//    DFA(M.Σ,
//        M.Q.Add q,
//        M.q0,
//        (if isFinal then M.F.Add q else M.F),
//        List.foldBack (fun (a, q_next) ->
//            Map.add (q, a) q_next) mappings M.δ)
let addState q mappings isFinal M =
    { M with
        Q = M.Q.Add q;
        F = (if isFinal
             then M.F.Add q
             else M.F);
        δ = List.foldBack (fun (a, q_next) -> Map.add (q, a) q_next)
                          mappings
                          M.δ }
    
//let removeState q (M : DFA) = //exception q=q0
//    DFA(M.Σ,
//        M.Q.Remove q,
//        M.q0,
//        M.F.Remove q,
//        Set.foldBack (fun a -> Map.remove (q, a)) M.Σ M.δ)
let removeState q M = //exception q=q0
    { M with
        Q = M.Q.Remove q;
        F = M.F.Remove q;
        δ = Set.foldBack (fun a -> Map.remove (q, a)) M.Σ M.δ }

let addString (M:DFA) ω =
        
    ///returns a cloned state (with all transitions created)
    ///if the argument is a nonabsorption state or a queue state
    ///if it operates on the absorption state (None)
//        let clone q =
//            let q' = Set.maxElement this.Q + 1
//            q |> Option.iter (fun q ->
//                for a in this.Σ do
//                    this.δ (Some q) a
//                    |> Option.iter (fun q_next ->
//                        this.Transitions <- this.Transitions.Add ((q', a), q_next))
//                if this.F.Contains q then this.F <- this.F.Add q')
//            this.Q <- this.Q.Add q'
//            q'

    let R = ref M.Q
//    let q0' = Set.maxElement M.Q + 1
//    let passed = List.scan M.δ (Some M.q0) ω
//    let added = [q0' .. q0' + ω.Length]
//    let (clonedTrs, addedF) =
//        (passed, added)
//        ||> List.fold2
//                (fun (trs, (sts:Set<int>)) q q' ->
//                    match q with
//                    | None -> trs, sts
//                    | Some v -> 
//                        (Seq.fold (fun trs' a ->
//                            Option.foldBack
//                                (Map.add (q', a))
//                                (M.δ (Some v) a)
//                                trs')
//                            trs M.Σ),
//                        (if sts.Contains v
//                         then Set.add q' sts
//                         else sts))
//                (M.Transitions, M.F)
//    let newStates = 
//    let newF = Set.add (Set.maxElement newStates + 1) addedF
//    let newTrs =
//        (Seq.pairwise added, ω)
//        ||> Seq.fold2 (fun ts (q, q_next) ω_i ->
//                            Map.add (q, ω_i) q_next ts) clonedTrs

    ///takes state q, cloned state q', transitions δ, alphabet Σ and returns
    ///the union of δ and all transitions coming from q where q is replaced by q'
//    let cloneTrs q q' =
//        Seq.fold (fun δ a ->
//            Option.foldBack
//                (Map.add (q', a))
//                (δ.TryFind (q, a))
//                δ)

    let cloneTrs q M =
        Set.fold (fun trs a ->
                    match M.δ.TryFind (q, a) with
                    | Some v -> (a, v)::trs
                    | None -> trs)
                 [] M.Σ
//        [for a in M.Σ do
//            match M.δ.TryFind (q, a) with
//            | Some v -> yield (a, v)
//            | None -> ()]

    ///takes state q, alphabet Σ, transitions δ and returns
    ///the difference of δ and all transitions coming from q
    let removeTrs q = Seq.foldBack (fun a -> Map.remove (q, a))

    let rec clone M q q' ω added =
        match ω with
        | [] -> addState q' [] true M, q'::added
        | ω_i::tail ->
            let (isFinal, q_next, mps) =
                match q with
                | None -> false, None, []
                | Some v -> M.F.Contains v,
                            M.δ.TryFind (v, ω_i),
                            cloneTrs v M
            clone (addState q' ((ω_i, q' + 1)::mps) (isFinal) M)
                  q_next
                  (q' + 1)
                  tail
                  (q'::added)

//    List.fold (fun (states, transitions, q) ->
//        let q' = Set.maxElement states + 1
//        let q_next = M.δ q ω_i
//        ((Set.add q' states), (Map.add transitions, q))
//        (M.Q, M.Transitions, q0) ω

//    this.F <- this.F.Add
//        <| List.fold (fun q_last ω_i ->
//                let q = clone (this.δ (Some q_last) ω_i)
//                this.Transitions <- this.Transitions.Add ((q_last, ω_i), q)
//                q)
//                q0' ω
        
    ///takes state q, transitions δ and checks
    ///whether δ has transitions incoming into q or not
    let unreachable q = not << Map.exists (fun _ -> (=) q)
            
    ///takes alphabet Σ, input string ω, states Q, register R,
    ///transitions δ, start state q and recursivly removes
    ///all unreacheable states from Q, R and δ, moving by ω
    let rec eliminate q ω R M =
        match q with
        | Some v when unreachable v M.δ ->
            match ω with
            | [] -> Set.remove v R, removeState v M
            | ω_i::tail -> eliminate (M.δ.TryFind (v, ω_i))
                                     tail
                                     (R.Remove v)
                                     (removeState v M)
        | _ -> R, M

            
    (*ω |> Seq.scan (fun q ω_i ->
        Option.bind(fun q ->let q_next
         = this.δ q ω_i
                            this.Q <- this.Q.Remove q
                            for a in this.Σ do
                                this.Transitions <- this.Transitions.Remove (q, a)
                            R := (!R).Remove q
                            q_next) q) (Some q0)*)
//    ω
//    |> Seq.scan (fun q ω_i ->
//        let q_next = this.δ q ω_i
//        this.Q <- this.Q.Remove q.Value
//        for a in this.Σ do
//            this.Transitions <- this.Transitions.Remove (q.Value, a)
//        R := (!R).Remove q.Value
//        q_next) (Some q0)
//    |> Seq.takeWhile (Option.fold (fun _ -> unreacheable) false)
//    |> Seq.iter (ignore)
//    this.q0 <- q0'

//        let rec clearEdges node hopList =
//            if List.isEmpty hopList || Map.exists (fun _ dst -> dst = node) this.Transitions then this.Transitions
//            else let tr' = Map.filter (fun (src, _) _ -> src <> node ) this.Transitions
//                 match Map.tryFind (node, hopList.Head) this.Transitions with
//                 | None -> tr'
//                 | Some node -> clearEdges tr' node hopList.Tail

    ///checks for the equivalence of states by comparing
    ///(i) whether both states are accepting or not, and
    ///(ii) whether the outgoing transitions lead to the same state in R
    let equiv M p q =
        (M.F.Contains p = M.F.Contains q)
        && not <| Set.exists (fun a ->
            M.δ.TryFind (q, a) <> M.δ.TryFind (p, a)) M.Σ

    ///redirect into p transitions coming into q
    let merge p q δ =
        Map.map (fun _ -> function
                    | q_next when q_next = q -> p
                    | q_next -> q_next)
                 δ

    ///If the argument state q is found to be equivalent to a state p
    ///in the register R, function merge(p; q) is called;
    ///if not, it is simply added to the register
    let rec repreg states R (M : DFA) =
        match states with
        | [] -> M
        | q::tail ->
            match R |> Set.toSeq |> Seq.tryFind (equiv M q) with
            | Some p -> repreg tail
                               R
                               { M with δ = (merge p q M.δ) }
            | None -> repreg tail (R.Add q) M
        
//    for i in ω.Length .. -1 .. 1 do
//        this.δ' (Some this.q0) (Seq.take i ω |> Seq.toList)
//        |> Option.iter (replace_or_register)
    //List.fold (fun q ω_i -> Option.bind (fun q -> Map.tryFind (q, ω_i) δ') q) (Some q0') ω

    //let q0' = Set.maxElement M.Q + 1
    let q0' = M.Q.MaximumElement + 1
    let (M', added) = clone M (Some M.q0) q0' ω []
    eliminate (Some M.q0) ω M.Q { M' with q0 = q0'}
    ||> repreg (List.rev added)

[<EntryPoint>]
let main argv = 
    //printfn "%A" argv
    let ts = Map.ofList [
              (0, 'b'), 1;
              (1, 'a'), 2;
              (2, 'r'), 3;
              (2, 'b'), 4;
              (4, 'a'), 5;
              (5, 'b'), 4;
    ]
    let M = { Σ = set ['a';'b';'r']; Q = set [0..5]; q0 = 0; F = set [2;3;5]; δ = ts }
    //M.Accept ['b';'a';'b';'a'] |> ignore
    let M' = addString M ['b';'r';'a']
    printfn "%A" M'.Q
    M'.δ |> Map.iter (printfn "%A -> %A")
    Console.ReadLine() |> ignore
    0 // возвращение целочисленного кода выхода