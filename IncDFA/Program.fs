open System

type DFA =
    { Σ : Set<char>; //alphabet that is set of symbols
      Q : Set<int>; //states that are marked by int numbers
      q0 : int; //initial state from Q
      F : Set<int>; //final states from Q
      δ : Map<int * char, int> //transitions that are mapping between
                               //pairs (state, symbol) and states
    }
        
    ///<summary> Trying to accept the input string </summary>
    ///<param name="ω"> Input string </param>
    ///<returns> True if ω is accepted by automaton or False in other case </returns>
    member M.Accept ω =
        ///function returns extended mapping δ*(q, ω)
        let rec f ω q =
            match ω with
            | [] -> (Some q)
            ///return None or recursivly applies f to result of mapping
            | a :: x -> M.δ.TryFind (q, a) |> Option.bind (f x)
        ///finds δ*(q0, ω) and checks that result is a final state
        f ω M.q0 |> Option.fold (fun _ -> M.F.Contains) false

    ///prints automaton's specification
    override M.ToString() =
        sprintf "Alphabet: %A\nQ: %A \nq0: %A\nF: %A\nTransitions: " M.Σ M.Q M.q0 M.F
        + (Map.fold (fun acc k v -> acc + sprintf "\n  %A -> %A" k v) "" M.δ)

///adds given state q to automaton M. If "isFinal" is set to true,
///also adds it to the final states
let addState q isFinal M =
    { M with
        Q = M.Q.Add q;
        F = if isFinal then M.F.Add q else M.F }

///removes given state q from automaton M. If q is initial state,
///generates an InvalidOperationException
let removeState q M =
    if q <> M.q0
    then { M with
            Q = M.Q.Remove q;
            F = M.F.Remove q;
            δ = Set.foldBack (fun a -> Map.remove (q, a)) M.Σ M.δ }
    else invalidOp "The initial state cannot be removed"

///adds given transition ((q1, a), q2) to automaton M. If states q1, q2
///or symbol a are not in the automaton, generates an ArgumentException
let addTransition ((q1, a), q2) M =
    if M.Q.Contains q1 && M.Q.Contains q2 && M.Σ.Contains a
    then { M with δ = Map.add (q1, a) q2 M.δ }
    else invalidArg "((q1, a), q2)" "The transition contains wrong elements"

///takes boolean flag, automaton M and string ω and adds
///or removes ω to\from M depends on the value of the flag
let addOrRemove flag M ω =

    ///takes state q, cloned state q', automaton M and returns
    ///new automaton with the union of δ and all transitions
    ///coming from q where q is replaced by q'
    let cloneTrs q' q M =
        { M with δ = Set.foldBack (fun a ->
                        Option.foldBack (Map.add (q', a))
                                        (M.δ.TryFind (q, a)))
                                  M.Σ M.δ }

    ///takes string ω, list of already created states "added", new state q',
    ///state q, automaton M and recursivly adds q' to M for all δ*(q, ω)
    let rec clone flag ω added q' q M =
        match ω with
        //add the last of created states to automaton (and to final states
        //if flag = true, e.g. the string ω is added to automaton)
        | [] -> Option.foldBack (cloneTrs q') q (addState q' flag M), q'::added
        | a :: x ->
            match q with
            //if q is an absorption state (e.g. None),
            //add q' to automaton as a queue state
            | None -> None,
                      M |> addState q' false
            //if q is a nonabsorption state, add q' to automaton
            //as a cloned state of q with all transitions created
            | Some v -> M.δ.TryFind (v, a),
                        M |> addState q' (M.F.Contains v) |> cloneTrs q' v
            //create new state, add q' to list of created states and call
            ///the function again for new nonabsorption state (or None),
            ///augmented automaton and next symbol of ω
            ||> clone flag x (q'::added) (q' + 1)

    ///takes state q, transitions δ and checks
    ///whether δ has transitions incoming into q or has not
    let unreachable q = not << Map.exists (fun _ -> (=) q)
            
    ///takes state q, input string ω, register R, automaton M, and
    ///recursivly removes all unreacheable states from R and M for all δ*(q, ω)
    let rec eliminate q ω R M =
        match q with
        | Some v when unreachable v M.δ ->
            match ω with
            | [] -> Set.remove v R, removeState v M
            | a :: x -> eliminate (M.δ.TryFind (v, a))
                                  x
                                  (R.Remove v)
                                  (removeState v M)
        | _ -> R, M

    ///takes automaton M, state p from register, state q from Q
    ///and checks for the equivalence of p and q
    let equiv M p q =
        //both states are accepting or not
        (M.F.Contains p = M.F.Contains q)
        //all outgoing transitions lead to the same states
        && not <| Set.exists (fun a ->
            M.δ.TryFind (q, a) <> M.δ.TryFind (p, a)) M.Σ

    ///takes state p from R, state q from Q, automaton M and return new automaton
    ///where q is removed and transitions coming into q are redirected into p
    let merge p q M =
        { M with
            Q = M.Q.Remove q;
            F = M.F.Remove q;
            δ = Map.map (fun _ -> function
                        | q_next when q_next = q -> p
                        | q_next -> q_next)
                    M.δ }

    ///takes reverse list of created cloned and queue states, register R,
    ///automaton M and recursivly merges equivalent states from list and R
    let rec repreg added (R : Set<int>) M =
        match added with
        | [] -> M
        | q :: tail ->
            match Seq.tryFind (equiv M q) R with
            //if q from added states and p from R are equivalent, merge them
            //and call the function again for rest states and new automaton
            | Some p -> repreg tail R (merge p q M)//{ M with δ = merge p q M.δ }
            //if not, q is added to the register R
            | None -> repreg tail (R.Add q) M

    let q0' = M.Q.MaximumElement + 1 //create new initial state
    //create new automaton with cloned and queue states and list of this states
    let (M', added) = clone flag ω [] q0' (Some M.q0) M
    //add transitions between cloned and queue states and change initial state for q0'
    { Seq.foldBack2 (fun a (q2, q1) ->
        addTransition ((q1, a), q2)) (List.rev ω) (List.pairwise added) M'
      with q0 = q0'}
    |> eliminate (Some M.q0) ω M.Q //remove those states that became unreacheable
    ||> repreg added //merge equivalent states and return resulting automaton

///takes automaton M and string ω and returns new automaton M'
///that is minimal, complete and such that L(M') = L(M) U {ω}
let addString = addOrRemove true

///takes automaton M and string ω and returns new automaton M'
///that is minimal, complete and such that L(M') = L(M) \ {ω}
let removeString = addOrRemove false

[<EntryPoint>]
let main argv =
    let M = { Σ = set ['a'; 'b'; 'r'];
              Q = set [0 .. 5];
              q0 = 0;
              F = set [2; 3; 5];
              δ = Map.ofList [ (0, 'b'), 1;
                               (1, 'a'), 2;
                               (2, 'r'), 3;
                               (2, 'b'), 4;
                               (4, 'a'), 5;
                               (5, 'b'), 4; ] }
    printfn "accept baba: %A" <| M.Accept ['b';'a';'b';'a']
    printfn "accept babb: %A" <| M.Accept ['b';'a';'b';'b']
    printf "%O" M
    printfn ""
    let M1 = addString M ['b';'r';'a']
    printf "%O" M1
    printfn "\n"
    let M2 = removeString M1 ['b';'a';'b';'a']
    printf "%O" M2
    Console.ReadLine() |> ignore
    0