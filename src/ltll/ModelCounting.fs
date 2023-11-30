module ModelCounting 

open System.Collections.Generic

open FsOmegaLib.DPA
open FsOmegaLib.SAT

type Semantics = 
    | Existential 
    | Universal

module Semantics = 
    let flip sem = 
        match sem with 
        | Existential -> Universal
        | Universal -> Existential


let findNonEmptyStates (sem : Semantics) (dpa : DPA<'T, 'L>) = 
    // All states that have some accpting run
    let findNonEmptyStatesExistential (dpa : DPA<'T, 'L>) = 
        // All even colors in the DPA
        let evemColors = 
            dpa.States
            |> Set.map (fun x -> dpa.Color.[x])
            |> Set.filter (fun x -> x % 2 = 0)
            |> Set.toList

        // All edges that are SAT
        let satEdges = 
            dpa.Edges
            |> Map.map (fun _ sucs -> 
                sucs 
                |> List.filter (fun (g, _) -> DNF.isSat g)
                )

        let statesWithAcceptingSelfloop = 
            evemColors
            |> List.map (fun col -> 

                let statesOfSmallerColor = 
                    dpa.States
                    |> Set.filter (fun s -> dpa.Color.[s] <= col)

                let reachPairs = 
                    GraphUtil.shortestPathsBetweenAllPairs statesOfSmallerColor (fun s -> satEdges.[s]) false

                // All states of col that hav an path to themself using only smaller colors
                let winningStates = 
                    dpa.States
                    |> Set.filter (fun s -> dpa.Color.[s] = col)
                    |> Set.filter (fun s -> reachPairs.ContainsKey (s, s))
                
                winningStates
                )
            |> Set.unionMany
        

        // Compute all states that can reach a state in 
        let reachPairs = 
            GraphUtil.shortestPathsBetweenAllPairs dpa.States (fun s -> satEdges.[s]) false

        dpa.States
        |> Set.filter (fun s -> 
            statesWithAcceptingSelfloop
            |> Set.exists (fun s' -> reachPairs.ContainsKey (s, s'))
        )

    // All states for which all runs are accepting 
    let findNonEmptyStatesUniversal (dpa : DPA<'T, 'L>) = 
        // Increment all colors
        let dpa' = {dpa with Color = dpa.Color |> Map.map (fun _ c -> c + 1)}

        // All states from which there exists some rejecting run
        let nonWinningStates = findNonEmptyStatesExistential dpa'

        dpa.States 
        |> Set.filter (fun s -> Set.contains s nonWinningStates |> not)


    match sem with 
    | Existential -> findNonEmptyStatesExistential dpa 
    | Universal -> findNonEmptyStatesUniversal dpa 



let countBoundedModels (sem : Semantics) (n : int) (dpa : DPA<'T, 'L>) = 
    let finalStates = findNonEmptyStates sem dpa

    let inputSpace = 
        Util.computeBooleanPowerSet (List.length dpa.APs)

    let initCounts = 
        dpa.States
        |> Seq.map (fun s -> s, if Set.contains s finalStates then 1 else 0)
        |> Map.ofSeq

    let res = 
        (initCounts, [0..n-1])
        ||> List.fold (fun currentCounts _ -> 
            //printfn $"%A{currentCounts}"
            dpa.States
            |> Seq.map (fun s -> 
                let newCounts = 
                    inputSpace
                    |> Seq.map (fun letter -> 
                        let sucState = dpa.Edges.[s] |> List.find (fun (g, _) -> g |> DNF.eval (fun i -> letter.[i]) ) |> snd
                        currentCounts.[sucState]
                        )
                    |> Seq.sum

                s, newCounts
                )
            |> Map.ofSeq
        )

    res.[dpa.InitialState]



// Count the number of words of the for uv^\omega with |u| = prefixLength and |v| = loopLength that are accepted by dpa
let countLassosOfGivenLength prefixLength loopLength (dpa : DPA<'T, 'L>) = 
    let inputSpace = 
        Util.computeBooleanPowerSet (List.length dpa.APs)

    let countModelsOfGuard (g : DNF<int>) = 
        // If we want to scale to many APs, use proper SAT-model counting here
        inputSpace
        |> Seq.filter (fun letter -> 
            g |> DNF.eval (fun i -> letter.[i])
            )
        |> Seq.length

    // Perform DFS on the unfolded tree
    // We need to maintain the visited combinations as a list to check acceptance
    let rec countLassosRec (visitedCombinations : list<'T * int>)  (currentState : 'T) (currentPosition : int) (currentConstraints : list<DNF<int>>) = 

        if List.contains (currentState, currentPosition) visitedCombinations then 
            // We have reached a cycle, and do not need to unfold further

            let index = List.findIndex ((=) (currentState, currentPosition)) visitedCombinations
            let relevantLassoCombinations = visitedCombinations[index..]

            // We check if the lasso is accepting
            let maxColor = 
                relevantLassoCombinations
                |> List.map fst 
                |> List.map (fun q -> dpa.Color.[q])
                |> List.max

            if maxColor % 2 <> 0 then 
                // The loop is not accepting 
                0
            else 
                // The loop is accepting 
                let modelCount = 
                    currentConstraints
                    |> List.map countModelsOfGuard
                    |> List.fold (*) 1

                modelCount
        else    
            let newVisitedCombinations =  visitedCombinations @ [(currentState, currentPosition)]
            let newCurrentPosition = (currentPosition + 1) % loopLength

            dpa.Edges.[currentState]
            |> Seq.map (fun (g, ss) -> 
                let newFormula : DNF<int> = DNF.constructConjunction [currentConstraints.[currentPosition]; g]
                
                if DNF.isSat newFormula |> not then 
                    // The current path does not admit any concrete solution
                    0
                else 
                    // Replace the i-th position with the new formula
                    let newConstraints = 
                        currentConstraints
                        |> List.mapi (fun i x -> if i = currentPosition then newFormula else x)

                    countLassosRec newVisitedCombinations ss newCurrentPosition newConstraints
                )
            // Sum over all symbolic paths
            |> Seq.sum 



    let initConstraint = 
        List.init loopLength (fun _ -> DNF.trueDNF)

    let hasher = new Dictionary<_, _>()

    let getNumberOfLassosFromState (s : 'T) = 
        if hasher.ContainsKey s then 
            hasher.[s]
        else 
            let res = countLassosRec [] s 0 initConstraint
            hasher.Add(s, res)
            res

    let rec explorePrefix (currentState : 'T) (step : int) = 
        if step >= prefixLength then 
            getNumberOfLassosFromState currentState
        else 
            dpa.Edges.[currentState]
            |> Seq.map (fun (g, ss) -> 
                
                let modelCount = countModelsOfGuard g 

                let recRes = explorePrefix ss (step + 1)

                recRes * modelCount
                )
            |> Seq.sum

    explorePrefix dpa.InitialState 0