open System

type DFA(Σ : Set<char>,
         Q : Set<int>,
         q0 : int,
         F : Set<int>,
         transitions : Map<int * char, int>) =
         
    ///Alphabet that is set of symbols
    member this.Σ = Σ
    
    ///States that are marked by int numbers
    member val Q = Q with get, set
    
    ///Initial state from Q
    member val q0 = q0 with get, set
    
    ///Final states from Q
    member val F = F with get, set
    
    ///Transitions that are mapping between pairs (state, symbol) and states
    member val Transitions = transitions with get, set
    
    ///<summary> Partial mapping </summary>
    ///<param name="q"> State to start from </param>
    ///<param name="a"> Input symbol </param>
    ///<returns> Some state if mapping exists or None in other case </returns>
    member this.δ q a =
        Option.bind (fun q -> this.Transitions.TryFind (q, a)) q
    
    ///<summary> Extended mapping </summary>
    ///<param name="q"> State to start from </param>
    ///<param name="ω"> Input string </param>
    ///<returns> Some state if mapping exists or None in other case </returns>
    member this.δ' q ω =
        match ω with
        | [] -> q
        | a :: x ->
            this.δ q a
            |> Option.bind (fun q_next -> this.δ' (Some q_next) x)
    
    ///<summary> Trying to accept the input string </summary>
    ///<param name="ω"> Input string </param>
    ///<returns> True if ω is accepted by automaton or False in other case </returns>
    member this.Accept ω =
        this.δ' (Some q0) ω
        |> Option.fold (fun _ q -> F.Contains q) false
       
    ///
    member this.AddString ω =
        
        ///returns a cloned state (with all transitions created)
        ///if the argument is a nonabsorption state or a queue state
        ///if it operates on the absorption state
        let clone q =
            let q' = Set.maxElement this.Q + 1
            q |> Option.iter (fun q ->
                for a in this.Σ do
                    this.δ (Some q) a
                    |> Option.iter (fun q_next ->
                        this.Transitions <- this.Transitions.Add ((q', a), q_next))
                if this.F.Contains q then this.F <- this.F.Add q')
            this.Q <- this.Q.Add q'
            q'

        let R = ref this.Q
        let q0' = clone (Some q0)
        this.F <- this.F.Add
            <| List.fold (fun q_last ω_i ->
                    let q = clone (this.δ (Some q_last) ω_i)
                    this.Transitions <- this.Transitions.Add ((q_last, ω_i), q)
                    q)
                    q0' ω
        
        ///function checks for the absence of incoming transitions
        let unreacheable q =
            not <| Map.exists (fun _ -> (=) q) this.Transitions
            
        (*ω |> Seq.scan (fun q ω_i ->
            Option.bind(fun q ->let q_next = this.δ q ω_i
                                this.Q <- this.Q.Remove q
                                for a in this.Σ do
                                    this.Transitions <- this.Transitions.Remove (q, a)
                                R := (!R).Remove q
                                q_next) q) (Some q0)*)
        ω
        |> Seq.scan (fun q ω_i ->
            let q_next = this.δ q ω_i
            this.Q <- this.Q.Remove q.Value
            for a in this.Σ do
                this.Transitions <- this.Transitions.Remove (q.Value, a)
            R := (!R).Remove q.Value
            q_next) (Some q0)
        |> Seq.takeWhile (Option.fold (fun _ -> unreacheable) false)
        |> Seq.iter (ignore)
        this.q0 <- q0'
        
        ///checks for the equivalence of states by comparing
        ///(i) whether both states are accepting or not, and
        ///(ii) whether the outgoing transitions lead to the same state in R
        let equiv p q =
            if this.F.Contains p <> this.F.Contains q then false
            else if Set.exists (fun a -> this.δ (Some q) a <> this.δ (Some p) a)
                               this.Σ then false
            else true
            
        ///redirect into p transitions coming into q
        let merge p q =
            this.Transitions <-
                Map.map (fun _ -> function
                            | q_next when q_next = q -> p
                            | q_next -> q_next)
                        this.Transitions
            this.Q <- this.Q.Remove q
            
        ///If the argument state q is found to be equivalent to a state p
        ///in the register R, function merge(p; q) is called;
        ///if not, it is simply added to the register
        let replace_or_register q =
            match Set.toSeq !R
                  |> Seq.tryFind (equiv q) with
            | Some p -> merge p q
            | None -> R := (!R).Add q
        
        for i in ω.Length .. -1 .. 1 do
            this.δ' (Some this.q0) (Seq.take i ω |> Seq.toList)
            |> Option.iter (replace_or_register)

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
    let dfa1 = DFA(set ['a';'b';'r'], set [0..5], 0, set [2;3;5], ts)
    dfa1.Accept ['b';'a';'b';'a'] |> ignore
    dfa1.AddString ['b';'r';'a']
    printfn "%A" dfa1.Q
    printfn "%A" dfa1.Transitions
    Console.ReadLine() |> ignore
    0 // возвращение целочисленного кода выхода