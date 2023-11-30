module Trace 

open System

open FsOmegaLib.SAT
open FsOmegaLib.DPA
open FsOmegaLib.JSON
open FsOmegaLib.LTL

open Util
open ModelCounting

type Trace<'L> = 
    {
        APs : list<'L>
        Trace : list<Set<int>>
        Loop : list<Set<int>>
    }

let simulateTraceInDpa (dpa : DPA<'T, 'L>) (trace : Trace<'L>) (loop:bool)= 
    // Map the AP indeices in the DPA to that of the trace
    let apMapping = 
        [0..dpa.APs.Length - 1]
        |> Seq.map (fun l -> 
            l, 
            trace.APs
            |> List.tryFindIndex ((=) dpa.APs.[l])
            //|> Option.defaultWith (fun _ -> raise <| AnalysisException $"AP %A{dpa.APs.[l]} not defined in trace")
            )
        |> Map.ofSeq

    let rec sim (s : 'T) (t : list<Set<int>>) =     
        match t with 
        | [] -> s::[] 
        | x :: xs -> 
            let sucState = 
                dpa.Edges.[s]
                |> List.find (fun (g, _) -> 
                    g 
                    |> DNF.eval (fun i -> 
                        match apMapping.[i] with 
                        | Some j -> Set.contains j x
                        | None -> 
                            // The AP is not defined in the trace, we assume it is set to false
                            false
                    )
                )
                |> snd

            s::sim sucState xs
    if loop then
        //printfn $"{trace.Loop}"
        //printfn $"{sim dpa.InitialState trace.Loop}"
        sim dpa.InitialState trace.Loop
    else 
        //printfn $"{trace.Trace}"
        //printfn $"{sim dpa.InitialState trace.Trace}"
        sim dpa.InitialState trace.Trace

let satisfiesLassoTraces(dpa : DPA<'T, 'L>) (traces : list<Trace<'L>>)=
    

    traces 
    |> List.forall (fun tr -> 
        let simState = simulateTraceInDpa dpa tr false|> List.last
        let newDpa = {Skeleton = dpa.Skeleton; InitialState = simState; Color=dpa.Color}
        let loopLength= tr.Loop |> List.length
        let apMapping = 
            [0..newDpa.APs.Length - 1]
            |> Seq.map (fun l -> 
                l, 
                tr.APs
                |> List.tryFindIndex ((=) newDpa.APs.[l])
                //|> Option.defaultWith (fun _ -> raise <| AnalysisException $"AP %A{newDpa.APs.[l]} not defined in trace")
                )
            |> Map.ofSeq
        let rec countLassosRec (visitedCombinations : list<'T * int>)  (currentState : 'T) (currentPosition : int)  = 
            
            if List.contains (currentState, currentPosition) visitedCombinations then 
                // We have reached a cycle, and do not need to unfold further

                let index = List.findIndex ((=) (currentState, currentPosition)) visitedCombinations
                let relevantLassoCombinations = visitedCombinations[index..]

                // We check if the lasso is accepting
                let maxColor = 
                    relevantLassoCombinations
                    |> List.map fst 
                    |> List.map (fun q ->newDpa.Color.[q])
                    |> List.max

                if maxColor % 2 <> 0 then 
                    //printfn$"maxColor: {maxColor}"
                    //printfn$"visitedCombinations {visitedCombinations}"
                    //printfn$"relevantLassoCombinations:{relevantLassoCombinations}, ({currentState},{currentPosition}, {dpa}, {tr}, {simState})"
                    // The loop is not accepting 
                    false
                else 
                    // The loop is accepting 
                    true
            else    
                let newVisitedCombinations =  visitedCombinations @ [(currentState, currentPosition)]
                let newCurrentPosition = (currentPosition + 1) % loopLength

                let assignment =tr.Loop[currentPosition]
                let sucState = 
                    newDpa.Edges.[currentState]
                    |> List.find (fun (g, _) -> 
                        g 
                        |> DNF.eval (fun i -> 
                            match apMapping.[i] with 
                            | Some j -> Set.contains j  assignment
                            | None -> 
                                // The AP is not defined in the trace, we assume it is set to false
                                printfn$"falsee"
                                false
                        )
                    )
                    |> snd //finde dnf, die pos in Trace satisfied:
                countLassosRec newVisitedCombinations sucState newCurrentPosition
                // dpa.Edges.[currentState]
                // |> Seq.map (fun (g, ss) -> 
                //     let newFormula : DNF<int> = DNF.constructConjunction [currentConstraints.[currentPosition]; g]
                    
                //     if DNF.isSat newFormula |> not then 
                //         // The current path does not admit any concrete solution
                //         0
                //     else 
                //         // Replace the i-th position with the new formula
                //         let newConstraints = 
                //             currentConstraints
                //             |> List.mapi (fun i x -> if i = currentPosition then newFormula else x)

                //         countLassosRec newVisitedCombinations ss newCurrentPosition newConstraints
                //     )
                // // Sum over all symbolic paths
                // |> Seq.sum
            
        countLassosRec [] simState 0  
        
        
        
        
        
        //alt:kaputt
        (* let loopSet = simulateTraceInDpa newDpa tr true
        //
        let ColorList =
            loopSet
            |> List.map (fun x -> newDpa.Color.[x])
        let maxColor = ColorList |> List.max 
        maxColor % 2 = 0 *)
        )
    


let satisfiesTraces (sem : Semantics) (dpa : DPA<'T, 'L>) (traces : list<Trace<'L>>) = 
    let goodStates = ModelCounting.findNonEmptyStates sem dpa 

    traces 
    |> List.forall (fun tr -> 
        let simState = simulateTraceInDpa dpa tr false |> List.last
        Set.contains simState goodStates
        )


let checkLtlOnTrace (sem : Semantics) (trace : Trace<'L>) (formula : LTL<'L>) = 

    let rec checkPosition (sem : Semantics) i (f : LTL<'L>) = 
        // We assert that the index is in range
        assert (i < trace.Trace.Length)

        match f with 
        | Atom x -> 
            match trace.APs |> List.tryFindIndex ((=) x) with 
            | Some apIndex ->trace.Trace.[i].Contains apIndex
            | None -> 
                // The AP is not defined on the trace and thus not set
                false
        | True -> true 
        | False -> false 
        | And(e1, e2) -> 
            checkPosition sem i e1 && checkPosition sem i e2
        | Implies(e1, e2) -> 
            (checkPosition sem i (Not e1)) || checkPosition sem i e2
            //not (checkPosition sem i e1) || checkPosition sem i e2
        | Equiv(e1, e2) -> 
            let res1 = checkPosition sem i e1
            let res2 = checkPosition sem i e2
            (res1 && res2) || (not res1 && not res2)
        | Xor(e1, e2) -> 
            let res1 = checkPosition sem i e1
            let res2 = checkPosition sem i e2
            (res1 && not res2) || (not res1 && res2)
        | Or(e1, e2) -> 
            checkPosition sem i e1 || checkPosition sem i e2
        | U(e1, e2) -> 
            
            let satIndex = 
                [i..trace.Trace.Length - 1]
                |> List.tryFind (fun j -> checkPosition sem j e2)

            match satIndex, sem with 
            | None, Universal -> false 
            | Some j, Universal | Some j, Existential -> 
                [i..j-1]
                |> List.forall (fun k -> checkPosition sem k e1)
            | None, Existential -> 
                [i..trace.Trace.Length-1]
                |> List.forall (fun k -> checkPosition sem k e1)
        | W(e1, e2) -> 
            checkPosition sem i (G e2) || checkPosition sem i (U(e1, e2))
        | M _ -> failwith ""
        | R _ -> failwith ""
        | F e -> 
            match sem with 
            | Universal -> 
                // This does not need to hold but we overapprxoimate
                [i..trace.Trace.Length - 1]
                |> List.exists (fun k -> checkPosition sem k e)
            | Existential -> 
                true
        | G e -> 
            match sem with 
            | Universal -> 
                // This does not need to hold but we overapprxoimate
                false
            | Existential -> 
                [i..trace.Trace.Length - 1]
                |> List.forall (fun k -> 
                (* printfn $"check on Position: {k} , {checkPosition sem k e}"
                printfn $"{ [i..trace.Trace.Length - 1]}, {e}" *)
                checkPosition sem k e)
                
        | X e -> 
            if i = trace.Trace.Length - 1 then 
                match sem with 
                | Existential -> true 
                | Universal -> false
            else 
                checkPosition sem (i + 1) e
        | Not e -> checkPosition (Semantics.flip sem) i e |> not

    checkPosition sem 0 formula


module Parser = 
    open FParsec

    let ws = spaces 

    let idParser = many1Chars (letter <|> digit) 

    let stepParser = 
        between (skipChar '{' .>> ws) (skipChar '}') (sepBy (idParser .>> ws) (skipChar ',' .>> ws))

    let traceParser = 
        many1 (stepParser .>> ws)
        |>> fun x -> 
            let aps = List.concat x |> List.distinct

            {
                Trace.APs = aps 
                Trace = 
                    x
                    |> List.map (fun y -> 
                        y 
                        |> List.map (fun ap -> List.findIndex ((=) ap) aps)
                        |> set
                        )
                Loop = []
            }


    let tracesParser = 
        sepBy1 (traceParser .>> ws) (skipChar ';' .>> ws)

    let parseTraces s = 
        let full = ws >>. tracesParser .>> ws .>> eof
        let res = run full s
        match res with
        | Success (res, _, _) -> Result.Ok res
        | Failure (err, _, _) -> Result.Error err

    let getTracesFromJsonString s = 
        let getTraceFromString (s : String) = 
            let tr = 
                s.Split ';' 
                |> Array.toList 
                |> List.map (fun x -> x.Trim())
                |> List.map (fun x -> 
                    x.Split ','
                    |> Array.toList
                    |> List.map (fun x -> x.Trim())
                    |> List.filter (fun x -> x <> "")
                    )
                

            let aps = List.concat tr |> List.distinct

            {
                Trace.APs = aps 
                Trace = 
                    tr
                    |> List.map (fun y -> 
                        y 
                        |> List.map (fun ap -> List.findIndex ((=) ap) aps)
                        |> set
                        )
                Loop = []
            }


        FsOmegaLib.JSON.Parser.parseJsonString s
        |> Result.bind (fun json -> 
            try 
                json
                |> JSON.lookup "traces"
                |> JSON.getList
                |> List.map JSON.getString
                |> List.map getTraceFromString
                |> Result.Ok
            with 
            | JsonError -> Result.Error "Could not obtain traces from JSON"
        )





