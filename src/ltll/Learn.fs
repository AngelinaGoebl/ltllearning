module Learn 

open System
open System.Collections.Generic
open MathNet.Numerics.LinearAlgebra

open FsOmegaLib.SAT
open FsOmegaLib.LTL
open FsOmegaLib.DPA
open FsOmegaLib.Operations

open Util
open Configuration
open ModelCounting
open Trace 
open Grammar
type DPAState = 
    | Original of int
    | New of int

type LearningOptions = 
    {
        RankingMethod : string 
        SamplingMethod : string 
        NumberOfSamples : int
        IncludeAllSubformulas : bool
        Length: int
        NumberOfTraces: int
    }

type EvalResult = 
    {
        Size : int
        Formula : LTL<string>
        Count : float
    }

type ScoreResult = 
    {
        Information: EvalResult
        Specificity: double 
        Simplicity : double
        OverallScore: double
    }
type SemanticsSetting =
 | Universal
 | Existential
 | Infinite

let probWeight = 0.1


let rec boundedSafetyProperty ltl =
    match ltl with
    | Atom _ -> true
    | True -> true
    | False -> true
    | And(e1,e2) -> boundedSafetyProperty e1 && boundedSafetyProperty e2
    | Or(e1,e2) -> boundedSafetyProperty e1 && boundedSafetyProperty e2
    | Equiv(e1,e2) -> boundedSafetyProperty e1 && boundedSafetyProperty e2
    | Xor(e1,e2) -> boundedSafetyProperty e1 && boundedSafetyProperty e2
    | Implies(e1,e2) -> boundedSafetyProperty e1 && boundedSafetyProperty e2
    | Not(e1) -> boundedSafetyProperty e1 
    | X e1 -> boundedSafetyProperty e1 
    | _ -> false

let rec invariant (ltl: LTL<'a>) =  
    match ltl with
    | G (e: LTL<'a>)-> boundedSafetyProperty e
    | And(e1: LTL<'a>,e2: LTL<'a>) -> invariant e1 || invariant e2
    | Or(e1: LTL<'a>,e2: LTL<'a>) -> invariant e1 && invariant e2
    | X e1-> invariant e1
    | Not e1 -> guarantee e1
    | Implies(e1,e2) -> invariant (Or(Not e1, e2))
    | Equiv(e1,e2) -> invariant (And (Implies(e1,e2), Implies(e2,e1)))
    | Xor(e1,e2) -> invariant (Or(And(e1,Not e2), And(Not e1, e2)))
    | _ -> false
and guarantee ltl =  
    match ltl with
    | F e-> boundedSafetyProperty e
    | And (e1,e2) -> guarantee e1 && guarantee e2
    | Or (e1,e2) -> guarantee e1 || guarantee e2
    | X e1-> guarantee e1
    | Not e1 -> invariant e1
    | Implies(e1,e2) -> guarantee(Or(Not e1, e2))
    | Equiv(e1,e2) -> guarantee (And (Implies(e1,e2), Implies(e2,e1)))
    | Xor(e1,e2) -> guarantee (Or(And(e1,Not e2), And(Not e1, e2)))
    | _ -> false
let rec persistence ltl = 
    match ltl with
        | F e-> invariant e
        | And(e1,e2) -> persistence e1 && persistence e2
        | Or (e1,e2) -> persistence e1 || persistence e2
        | X e1 -> persistence e1
        | Not e1 -> response e1 
        | _ -> false
and response ltl = 
    match ltl with
        | G e-> guarantee e
        | And(e1,e2) -> response e1 || response e2
        | Or (e1,e2) -> response e1 && response e2
        | X e1 -> response e1
        | Not e1 -> persistence e1
        | _ -> false

let rankResultsByNorm (results : list<EvalResult>) (maxCount: int)= 
    
    //build Scores:
    
    let maxSize = 
        results
        |> List.map (fun x -> x.Size)
        |> List.max 
    
    let resultsWithProb =
        results
         |> List.map (fun x -> (x,double(1)-double(double(x.Size)/double(maxSize)) ,double(1)-double(double(x.Count) /double( maxCount))))


    
    let maxNonSatPercentage = 
        resultsWithProb
        |> List.map (fun (_, _,countValue) -> countValue)
        |> List.max 
        (* results
        |> List.map (fun x -> x.NonSatPercentage)
        |> List.max  *)

    let maxProbability = 
     resultsWithProb
        |> List.map (fun (_, sizeValue,_) -> sizeValue)
        |> List.max 
        (* results
        |> List.map (fun x -> x.Probability)
        |> List.max  *)

    let rescaled = 
     resultsWithProb
        |> List.map (fun (x, sizeValue,countValue) -> (x, sizeValue / maxProbability, countValue/maxNonSatPercentage))
        
        (* results
        |> List.map (fun x -> 
            (x, x.Probability / maxProbability, x.NonSatPercentage / maxNonSatPercentage)
        ) *)

    

    
    
    
    let heuristic (prob, nonSatPercentage) = 
        probWeight * prob + (1.0 - probWeight) * nonSatPercentage

    let mutable rescaledHeuristic = []

    for (info, prob, nonSat) in rescaled do
        rescaledHeuristic<- {Information = info; Specificity= nonSat; Simplicity=prob; OverallScore=heuristic(prob,nonSat)} :: rescaledHeuristic

    (* let rescaledWithHeuristic=
        rescaled
        |> List.map (fun (x: EvalResult, prob:double, satPer: double) -> (x,prob,satPer,double(heuristic(prob,satPer))))
 *)
    let sortedRescaled =
     rescaledHeuristic
        |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled

let densityScore (results : list<EvalResult>) =
    let resultsWithProb =
        results
         |> List.map (fun x -> 
         (x,double(1)/double(x.Size) ,double(1)- double(x.Count)))
    let mutable rescaledHeuristic = []

    for (info, prob, nonSat) in resultsWithProb do
        rescaledHeuristic<- {Information = info; Specificity= nonSat; Simplicity=prob; OverallScore= prob*nonSat} :: rescaledHeuristic
    let sortedRescaled =
        rescaledHeuristic
            |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled
let densityScoreStrechedSize (results : list<EvalResult>) =
    let maxSize = 
        results
        |> List.map (fun x -> x.Size)
        |> List.max 

    let resultsWithProb =
        results
         |> List.map (fun x -> 
         (x,double(1)- (double(x.Size)/double(maxSize)) ,double(1)- double(x.Count)))
    let mutable rescaledHeuristic = []

    for (info, prob, nonSat) in resultsWithProb do
        rescaledHeuristic<- {Information = info; Specificity= nonSat; Simplicity=prob; OverallScore= prob*nonSat} :: rescaledHeuristic
    let sortedRescaled =
        rescaledHeuristic
            |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled

let regexScoreLinSize (results : list<EvalResult>)  =
    let maxSize = 
        results
        |> List.map (fun x -> x.Size)
        |> List.max 
    printfn $"maxsize: {maxSize}"
    let resultsModelCountingScore =
        results
         |> List.map (fun x -> 
         (x,double(1)-(double(x.Size)/double(maxSize)) ,double(1)/(double(x.Count))))

     
    

    (* let minMCScore =
        resultsModelCountingScore
        |> List.map (fun (_, mc) -> mc)
        |> List.min 

    let maxMCScore =
        resultsModelCountingScore
        |> List.map (fun (_, mc) -> mc)
        |> List.max 

    let rangeMC = maxMCScore - minMCScore *)
    let mutable rescaledHeuristic = []

    for (info, simplicity, specificity) in resultsModelCountingScore do
        rescaledHeuristic<- {Information = info; Specificity= specificity; Simplicity=simplicity; OverallScore= specificity * simplicity} :: rescaledHeuristic



    let sortedRescaled =
        rescaledHeuristic
        |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled
    
let densityLight0 (results : list<EvalResult>) (maxCount: int)= 
    
    //build Scores:
    let resultsWithProb =
        results
         |> List.map (fun x -> 
         (x,double(1)/double(x.Size),double(1)- (double(x.Count)/double(maxCount))))

    let mutable rescaledHeuristic = []

    for (info, prob, nonSat) in resultsWithProb do
        rescaledHeuristic<- {Information = info; Specificity= nonSat; Simplicity=prob; OverallScore= prob*nonSat} :: rescaledHeuristic

    (* let rescaledWithHeuristic=
        rescaled
        |> List.map (fun (x: EvalResult, prob:double, satPer: double) -> (x,prob,satPer,double(heuristic(prob,satPer))))
 *)
    let sortedRescaled =
     rescaledHeuristic
        |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled


let densityLight (results : list<EvalResult>) (maxCount: int)= 
    
    //build Scores:
    
    let maxSize = 
        results
        |> List.map (fun x -> x.Size)
        |> List.max 
    printfn $"maxsize: {maxSize}"
    printfn $"maxCount {maxCount}"
    let resultsWithProb =
        results
         |> List.map (fun x -> 
         (x,double(1)-double(x.Size)/double(maxSize) ,double(1)- (double(x.Count)/double(maxCount))))

    let mutable rescaledHeuristic = []

    for (info, prob, nonSat) in resultsWithProb do
        rescaledHeuristic<- {Information = info; Specificity= nonSat; Simplicity=prob; OverallScore= prob*nonSat} :: rescaledHeuristic

    (* let rescaledWithHeuristic=
        rescaled
        |> List.map (fun (x: EvalResult, prob:double, satPer: double) -> (x,prob,satPer,double(heuristic(prob,satPer))))
 *)
    let sortedRescaled =
     rescaledHeuristic
        |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled

let densityLight2 (results : list<EvalResult>) (maxCount: int)= 
    
    //build Scores:
    
    let maxSize = 
        results
        |> List.map (fun x -> x.Size)
        |> List.max 
    printfn $"maxsize: {maxSize}"
    printfn $"maxCount {maxCount}"
    let resultsWithProb =
        results
         |> List.map (fun x -> 
         (x,double(1) / (double(2)**double(x.Size)) ,double(1)- (double(x.Count) /double(maxCount))))

    let mutable rescaledHeuristic = []

    for (info, prob, nonSat) in resultsWithProb do
        rescaledHeuristic<- {Information = info; Specificity= nonSat; Simplicity=prob; OverallScore= prob*nonSat} :: rescaledHeuristic

    (* let rescaledWithHeuristic=
        rescaled
        |> List.map (fun (x: EvalResult, prob:double, satPer: double) -> (x,prob,satPer,double(heuristic(prob,satPer))))
 *)
    let sortedRescaled =
     rescaledHeuristic
        |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled

let densityLight3 (results : list<EvalResult>) (maxCount: int)= 
    
    //build Scores:
    
    let maxSize = 
        results
        |> List.map (fun x -> x.Size)
        |> List.max 
    printfn $"maxsize: {maxSize}"
    printfn $"maxCount {maxCount}"
    let resultsWithProb =
        results
         |> List.map (fun x -> 
         (x,double(1) / (double(2)**double(x.Size)) ,(double(1)- (double(x.Count) /double(maxCount)))**(double(x.Size))))

    let mutable rescaledHeuristic = []

    for (info, prob, nonSat) in resultsWithProb do
        rescaledHeuristic<- {Information = info; Specificity= nonSat; Simplicity=prob; OverallScore= prob*nonSat} :: rescaledHeuristic

    (* let rescaledWithHeuristic=
        rescaled
        |> List.map (fun (x: EvalResult, prob:double, satPer: double) -> (x,prob,satPer,double(heuristic(prob,satPer))))
 *)
    let sortedRescaled =
     rescaledHeuristic
        |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled

let regexScoreRegulateSizeDensity(results : list<EvalResult>) (maxCount: int)=
    let resultsModelCountingScore =
        results
        |> List.map (fun x -> 
             (x,double(1) - (double(x.Count)/double(maxCount)), double(x.Size)))

    let minMCScore =
        resultsModelCountingScore
        |> List.map (fun (_, mc,_) -> mc)
        |> List.min 

    let maxMCScore =
        resultsModelCountingScore
        |> List.map (fun (_, mc,_) -> mc)
        |> List.max 

    let minSizeScore =
        resultsModelCountingScore
        |> List.map (fun (_, _, sizeScore) -> sizeScore)
        |> List.min 

    let maxSizeScore =
        resultsModelCountingScore
        |> List.map (fun (_, _,sizeScore) -> sizeScore)
        |> List.max 

    let rangeMC = maxMCScore - minMCScore
    let rangeSizeScore = maxSizeScore- minSizeScore

    let slope = - rangeMC / rangeSizeScore
    let intercept = - (slope *maxSizeScore) + minMCScore

    let resultsScaledSize=
        resultsModelCountingScore
        |> List.map (fun (x, mc,score) ->  if (rangeMC=0) then (x,mc, 1.0/score)  else (x,mc, slope*score + intercept)  )
 
    printfn $"({slope} * x + {intercept}), ({rangeMC}, {maxMCScore},{minMCScore}), ({rangeSizeScore}, {maxSizeScore},{minSizeScore})\n"


    let mutable rescaledHeuristic = []
    if (rangeMC=0) then
        for (info, specificity, simplicity) in resultsScaledSize do
        rescaledHeuristic<- {Information = info; Specificity= specificity; Simplicity=simplicity; OverallScore= simplicity} :: rescaledHeuristic
    else 
        for (info, specificity, simplicity) in resultsScaledSize do
        rescaledHeuristic<- {Information = info; Specificity= specificity; Simplicity=simplicity; OverallScore= (specificity) * simplicity} :: rescaledHeuristic



    let sortedRescaled =
        rescaledHeuristic
        |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled



// Generate candodates by sampling from custom grammar
// Higher weight is "better"


let regexScoreLight(results : list<EvalResult>)  =
    let resultsModelCountingScore =
        results
        |> List.map (fun x -> 
            if x.Count=0 then (x,double(1), double(1/x.Size)) else (x,double(1)/double(x.Count), double(1)/ double(x.Size)))

    (* let minMCScore =
        resultsModelCountingScore
        |> List.map (fun (_, mc) -> mc)
        |> List.min 

    let maxMCScore =
        resultsModelCountingScore
        |> List.map (fun (_, mc) -> mc)
        |> List.max 

    let rangeMC = maxMCScore - minMCScore *)
    let mutable rescaledHeuristic = []

    for (info, specificity, simplicity) in resultsModelCountingScore do
        rescaledHeuristic<- {Information = info; Specificity= specificity; Simplicity=simplicity; OverallScore= specificity * simplicity} :: rescaledHeuristic



    let sortedRescaled =
        rescaledHeuristic
        |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled

let regexScoreSameRange(results : list<EvalResult>)  =
    let resultsModelCountingScore =
        results
        |> List.map (fun x -> 
            if x.Count=0 then (x,double(1), double(1/x.Size)) else (x,double(1)/double(x.Count), double(1)/ double(x.Size)))

    let minMCScore =
        resultsModelCountingScore
        |> List.map (fun (_, mc,_) -> mc)
        |> List.min 

    let maxMCScore =
        resultsModelCountingScore
        |> List.map (fun (_, mc,_) -> mc)
        |> List.max 

    let minSizeScore =
        resultsModelCountingScore
        |> List.map (fun (_, _, sizeScore) -> sizeScore)
        |> List.min 

    let maxSizeScore =
        resultsModelCountingScore
        |> List.map (fun (_, _,sizeScore) -> sizeScore)
        |> List.max 

    let rangeMC = maxMCScore - minMCScore
    let rangeSizeScore = maxSizeScore- minSizeScore

    let slope = (rangeMC / rangeSizeScore) 
    let intercept = - (slope *minSizeScore) + minMCScore

    let resultsScaledSize=
        resultsModelCountingScore
        |> List.map (fun (x, mc,score) -> (x,mc, slope*score + intercept) )
 
    printfn $"({slope} * x + {intercept}), ({rangeMC}, {maxMCScore},{minMCScore}), ({rangeSizeScore}, {maxSizeScore},{minSizeScore})\n"


    let mutable rescaledHeuristic = []

    for (info, specificity, simplicity) in resultsScaledSize do
        rescaledHeuristic<- {Information = info; Specificity= specificity; Simplicity=simplicity; OverallScore= specificity * simplicity} :: rescaledHeuristic



    let sortedRescaled =
        rescaledHeuristic
        |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled


let regexScoreRegulateSize(results : list<EvalResult>)  =
    let resultsModelCountingScore =
        results
        |> List.map (fun x -> 
            if x.Count=0 then (x,double(1), double(x.Size)) else (x,double(1)/double(x.Count), double(x.Size)))

    let minMCScore =
        resultsModelCountingScore
        |> List.map (fun (_, mc,_) -> mc)
        |> List.min 

    let maxMCScore =
        resultsModelCountingScore
        |> List.map (fun (_, mc,_) -> mc)
        |> List.max 

    let minSizeScore =
        resultsModelCountingScore
        |> List.map (fun (_, _, sizeScore) -> sizeScore)
        |> List.min 

    let maxSizeScore =
        resultsModelCountingScore
        |> List.map (fun (_, _,sizeScore) -> sizeScore)
        |> List.max 

    let rangeMC = maxMCScore - minMCScore
    let rangeSizeScore = maxSizeScore- minSizeScore

    let slope = - rangeMC / rangeSizeScore
    let intercept = - (slope *maxSizeScore) + minMCScore

    let resultsScaledSize=
        resultsModelCountingScore
        |> List.map (fun (x, mc,score) ->  
            //if (rangeMC=0) then (x,mc, 1.0/score)  else 
            (x,mc, slope*score + intercept) 
             )
 
    printfn $"({slope} * x + {intercept}), ({rangeMC}, {maxMCScore},{minMCScore}), ({rangeSizeScore}, {maxSizeScore},{minSizeScore})\n"


    let mutable rescaledHeuristic = []
   (*  if (rangeMC=0) then
        for (info, specificity, simplicity) in resultsScaledSize do
        rescaledHeuristic<- {Information = info; Specificity= specificity; Simplicity=simplicity; OverallScore= simplicity} :: rescaledHeuristic
    else  *)
    for (info, specificity, simplicity) in resultsScaledSize do
        rescaledHeuristic<- {Information = info; Specificity= specificity; Simplicity=simplicity; OverallScore= (specificity) * simplicity} :: rescaledHeuristic



    let sortedRescaled =
        rescaledHeuristic
        |> List.sortByDescending (fun x -> x.OverallScore)

    sortedRescaled

let generateWeightedCandidatesByGrammar (aps : list<string>) numberOfSamples = 
    let grammar = Grammar.exampleLTLGrammar aps

    let maxGrammarDepth = 5

    Grammar.sampleFromGrammar grammar maxGrammarDepth numberOfSamples

let generateWeightedCandidatesBySpot (config : Configuration) (aps : list<string>) numberOfSamples includeSubformulas random ltl= 
    let seed = 0 

    let formulas =(RandomFormula.getRandomFormula config.SolverConfiguration seed numberOfSamples aps random)


    config.LoggerN $"%i{formulas.Length} formulas returned by spot"

    let formulas = 
        if includeSubformulas then 
            config.LoggerN "Adding all subformulas"
            formulas
            |> List.map LTL.allSubformulas
            |> Set.unionMany
            |> Set.toList 
        else 
            formulas

    let formulas =
        ltl::formulas
        |> List.distinct
    config.LoggerN $"%i{formulas.Length} formulas returned by spot"
   (*  let maxSize = 
        formulas
        |> List.map LTL.size
        |> List.max 
        |> double *)

    let weightedFormulas =  
        formulas
        |> List.map (fun f -> 
            // The weight of smaller formulas should be larger
            let weight = LTL.size f  //1.0 - (LTL.size f |> double) / maxSize
            weight, f
            )
    
    weightedFormulas











let rec gentraceFromTrace (list: Literal<'a> list list list) aps (random : Random)=
        
        let genTrace list set = 
        // gegeben eine Liste an Aps und einem Set, werden random die Aps hinzugefügt
            let rec chooseRandom list set =
                match list with
                | [] -> set
                | x::xs -> 
                let newset = 
                    if (rnd.Next (2)=1) then
                        chooseRandom xs (Set.add x set)
                    else 
                        chooseRandom xs set
                chooseRandom xs newset
            chooseRandom list set
        //liste an Aps, die in Conjunction vorkommen
        let rec apsFromConjuction conjunction =
            match conjunction with 
            | [] -> []
            | (PL x)::xs -> x:: (apsFromConjuction xs)
            | (NL x)::xs -> x:: (apsFromConjuction xs)
        //liste an APs die nach conjunction gelten müssen
        let rec traceFromConjunction (conjunction: Literal<'a> list) =
            match conjunction with 
            | [] -> [] 
            | (PL x)::xs -> x:: (traceFromConjunction xs)
            | (NL _)::xs -> (traceFromConjunction xs)

        match list with
        | []-> []
        | (x::[])::xs ->

            let givenTracelist = (traceFromConjunction x) |> Set.ofList
            let genAps aps conjunction = Set.difference (Set.ofList aps ) (Set.ofList (apsFromConjuction conjunction)) |> Set.toList
            let newTrace =genTrace (genAps aps x) givenTracelist
            
            newTrace :: gentraceFromTrace xs aps random

        | y::xs -> 
            let x = (y.[random.Next (List.length y)])
            let givenTracelist = (traceFromConjunction x) |> Set.ofList
            let genAps aps conjunction = Set.difference (Set.ofList aps ) (Set.ofList (apsFromConjuction conjunction)) |> Set.toList
            let newTrace =genTrace (genAps aps x) givenTracelist
            
            newTrace :: gentraceFromTrace xs aps random
        
let sampleLassoInDPA (r : Random) (stemSteps : int) (loopSteps : int) (dpa : DPA<int, 'L>) = 
    // All edges that are SAT
        let satEdges = 
            dpa.Edges
            |> Map.map (fun _ sucs -> 
                sucs 
                |> List.filter (fun (g, _) -> DNF.isSat g)
                )

        /// Sample a random path form s to s using only states in `statesOfSmallerOrEqualColor`. We simply take `loopSteps` many steps, and afterwards take the shortest path back to s 
        let generateRandomPath (shortestPathDict : Dictionary<_,_>) (step : int) (initialState : int) (targetStates : Set<int>) =
            let rec randomWalk (count : int) (currentState) = 
                
                let potentialSuccessors = 
                    satEdges.[currentState]
                    |> Seq.filter (fun (_, x) -> 
                        targetStates
                        |> Seq.exists (fun t -> shortestPathDict.ContainsKey (x, t))
                    )
                    |> Seq.toList

                if List.isEmpty potentialSuccessors || count = step then 
                    [], currentState
                else 
                    let g, t = potentialSuccessors.[r.Next (List.length potentialSuccessors)]
                    let p, tt = randomWalk (count + 1) t
                    g :: p, tt

            let p, finalState = randomWalk 0 initialState
            if Set.contains finalState targetStates then 
                p, finalState
            else
                let reachableTargetStates = 
                    targetStates 
                    |> Seq.filter (fun t -> shortestPathDict.ContainsKey (finalState, t))
                    |> Seq.toList

                assert (List.length reachableTargetStates > 0)
                let t = reachableTargetStates.[r.Next (List.length reachableTargetStates)]
                p @ (shortestPathDict.[finalState, t] |> fst), t


        // For each state we check if there exist an accepting cycle of length > 0 to itself
        let selfLoopMap = 
            dpa.States
            |> Seq.filter (fun x -> dpa.Color[x] % 2 = 0)
            |> Seq.choose (fun s -> 
                let statesOfSmallerOrEqualColor = 
                    dpa.States
                    |> Set.filter (fun t -> dpa.Color.[t] <= dpa.Color[s])

                let reachPairs = 
                    GraphUtil.shortestPathsBetweenAllPairs statesOfSmallerOrEqualColor (fun t -> satEdges.[t]) false

                if reachPairs.ContainsKey (s, s) |> not then 
                    None 
                else 
                    let randomLoopSteps = r.Next(loopSteps)
                    //let finalPath, _ = generateRandomPath reachPairs loopSteps s (Set.singleton s)
                    let finalPath, _ = generateRandomPath reachPairs (randomLoopSteps+1)  s (Set.singleton s)
                    (s, finalPath)
                    |> Some
                )
            |> Map.ofSeq

        // Compute all states that can reach a state in 
        let reachPairs = 
            GraphUtil.shortestPathsBetweenAllPairs dpa.States (fun s -> satEdges.[s]) false
        let randomStemSteps = r.Next(stemSteps+1)
        if randomStemSteps=0 then
                 printfn $"Step size is 0"
        printfn $"Step size: {randomStemSteps}"
        let stem, finalState = generateRandomPath reachPairs randomStemSteps dpa.InitialState (Map.keys selfLoopMap |> set)
        if (dpa.Color[finalState]%2=0 |> not) then
            failwith $"dpa.Color[finalState]: {dpa.Color[finalState]}"
        printfn $"finalState: {finalState}, {stem},{selfLoopMap.[finalState]}"

        stem, selfLoopMap.[finalState]



let searchSCC (dpa : DPA<int, 'L>)  =
    let satEdges = 
            dpa.Edges
            |> Map.map (fun _ sucs -> 
                sucs 
                |> List.filter (fun (g, _) -> DNF.isSat g)
                )
    let reachPairs = 
            GraphUtil.shortestPathsBetweenAllPairs dpa.States (fun s -> satEdges.[s]) false

    let rec checkSCC (listp': int list) (p: int) = 
        match listp' with
        | [] -> true
        | x::xs -> 
            if (reachPairs.ContainsKey(x,p)) then 
                checkSCC xs p
            else 
                false
    let rec searchCSShelp (candidatesp' : int list) (p: int) =
        match candidatesp' with 
        | []->[]
        | x::xs -> 
            if (reachPairs.ContainsKey(p,x)) then
                x::(searchCSShelp xs p)
            else 
                searchCSShelp xs p
    
    let rec findSCC states candidates =
        match states with
        | [] -> []
        | x::xs ->
            if (reachPairs.ContainsKey(dpa.InitialState, x)) then
                let candidateCSS = searchCSShelp candidates x
                let searchedEmpty = (candidateCSS = [])
                if searchedEmpty then
                    findSCC xs candidates
                else
                    if checkSCC candidateCSS x then
                        (candidateCSS |> set )::findSCC (Set.difference (xs |> set) (candidateCSS |> set)|> Set.toList)  candidates
                    else 
                        findSCC xs candidates
            else
                findSCC xs candidates

    findSCC (dpa.States |> Set.toList) (dpa.States |> Set.toList)
let rec acceptingCSS (css: Set<int> list) (dpa : DPA<int, 'L>)=
    match css with
    | [] -> []
    | x::xs -> 
        let listcss = x |> Set.toList |> List.map (fun x -> dpa.Color.[x])
        if ((listcss |> List.max)%2 =0) then
            x:: acceptingCSS xs dpa
        else 
            acceptingCSS xs dpa

let generateUniversalTraces (aps: 'String list)  learnOptions  dpa goodStates (rnd: Random) =

    let rec allPath (length: int)  (current:int) =

        match length with
        | (-1) -> [[]]
        | n ->
            let successors = dpa.Skeleton.Edges[current]  |> List.map (fun (_,y)-> y) |> List.distinct
            
            
            let rec insertInfront (list: int list  list) current =
                match list with
                | [] -> []
                | x::xs -> (current::x) :: insertInfront xs current

            let rec paths nextList  = 
                match nextList with 
                | [] -> []
                | x::xs -> 
                
                let pathss = allPath (n-1) x |> List.distinct
                
                let fullpaths = (insertInfront pathss current) 
                fullpaths  @ (paths xs)

            paths successors
    
    let candidates = 
        allPath learnOptions.Length dpa.InitialState
        |> List.filter (fun x -> Set.contains (List.last x) goodStates)
    printfn $"number of left:// {List.length candidates}"
    for i in candidates do
        printfn $""
        for j in i do
            printf $"{j}"
    printfn $"number of alltraces: {List.length (allPath learnOptions.Length dpa.InitialState)}"
    //1. sichergehen, dass List.length cnadidates >0
    if (List.length candidates=0) then
        failwith "there do not exist matching traces"
    //2. rec function: die numberOfTraces often:


    let rec produceConjTrace trace dpa (r:Random) =
        match trace with 
        | [] -> []
        | _::[] -> []
        | current::next::xs ->
            let DNFentry = 
                dpa.Skeleton.Edges[current] |> List.filter (fun (_,y) -> y=next) |> List.map (fun (dnf,_) -> dnf)
            let entry = 
                if (List.length DNFentry>1) then
                    DNFentry.[ rnd.Next(List.length DNFentry)]
                else
                    List.head DNFentry
            entry::produceConjTrace (next::xs) dpa r

    let apsInt = [ 0.. List.length aps-1 ]
    let rec produceNumberDNFtraces (number:int) (candidates: int list list) (rnd: Random) (dpa) apsInt (aps: 'c list)=
        match number with
        | 0 -> []
        | n ->
        //2.1. random ein Element aussuchen
            let nextTrace = candidates.[rnd.Next (List.length candidates)]
        //2.2. die liste durchlaufen: für jeden Übergang: DNF random aussuchen
            let DNF = produceConjTrace nextTrace dpa rnd 

            


            {Trace = (gentraceFromTrace DNF apsInt rnd); APs = aps; Loop = []}::produceNumberDNFtraces (n-1) candidates rnd dpa apsInt aps
  
    produceNumberDNFtraces learnOptions.NumberOfTraces candidates rnd dpa apsInt aps

    // 3. dann wie für infinite: random path generaten
    

    
    
    
    
    
    
let generateExTraces aps learnOptions  dpa goodStates =

    if  not (Set.contains dpa.InitialState goodStates) then
        raise <| Util.AnalysisException "initial not in good state "
        exit 0

    
    //generate 
    let apsInt = [ 0..dpa.APs.Length-1 ]
    printfn $"list1: {apsInt}"

    let rec powerset = 
        function
        | [] -> [[]]
        | (x::xs) -> 
            let xss = powerset xs 
            List.map (fun xs' -> x::xs') xss @ xss

    let powersetList = powerset (apsInt) |> List.map Set.ofList

    let stayinGoodState trace dpa=
        let tr = {APs = aps; Trace =[trace]; Loop=[]}
        let state = Trace.simulateTraceInDpa dpa tr false|> List.last
        let inGoodState = Set.contains state goodStates
        inGoodState

    let generateSuccessor goodState=
        let modifiedDpa = FsOmegaLib.DPA.DPA.fixAPs aps {Skeleton =dpa.Skeleton; InitialState = goodState; Color=dpa.Color}
        let FilteredPowerset =
            powersetList
            |> List.filter (fun x -> stayinGoodState x modifiedDpa)
        FilteredPowerset

        

    //für alle good States :
    // 1.DPA: initial state anpassen
    // 2. filtered Poweset erstellen und in einer Map speichern: state -> 
    let listOfSuccessorsGoodStates =(Set.map(fun x -> (x,generateSuccessor x))  goodStates |> Set.toList )
    for (a,b)  in listOfSuccessorsGoodStates do
         printfn $"A: {a} B: {b}"
    let mapSuccessorsGoodStates = Map.ofList listOfSuccessorsGoodStates

    printfn $"{mapSuccessorsGoodStates}"
    let rnd = System.Random(3)
    let shuffleR (r : Random) xs = xs |> Seq.sortBy (fun _ -> r.Next())
    let createtrace number current =
        let rec trace number current =
            match number with
            | 0 -> []
            | n -> 
            let getSet = mapSuccessorsGoodStates[current] |> shuffleR (rnd) |> Seq.head //TODO simulate
            //printfn $"get Set: {getSet}"
            let tr = {APs = aps; Trace =[getSet]; Loop = []}
            let newDpa = {Skeleton = dpa.Skeleton; InitialState = current; Color=dpa.Color}
            let next = Trace.simulateTraceInDpa newDpa tr false |> List.last
            //let updateCurrent = TODO 
            getSet::(trace (n-1) next)
        {APs = dpa.APs; Trace =(trace number current); Loop=[]}

    let generateNtracesOfLength number length  =
        let rec trace number length  =
            match number with
            | 0 -> []
            | n -> 
            printfn $"created trace {n}, {createtrace length dpa.InitialState}"
            (createtrace length dpa.InitialState) :: (trace (n-1) length)
        trace number length
    let traces = generateNtracesOfLength learnOptions.NumberOfTraces learnOptions.Length 
    printfn $"tracesss"
    printfn $"{traces.Length}"
    for i in traces do
        printfn $"{i}"
    printfn $"----------"
    traces

let generateTraces aps ltl config learnOptions sem (rnd: Random)=
    

    
    let dpa = 
            match FsOmegaLib.Operations.LTLConversion.convertLTLtoDPA false config.SolverConfiguration.MainPath config.SolverConfiguration.Ltl2tgbaPath ltl with 
            | Success x -> FsOmegaLib.DPA.DPA.fixAPs aps x 
            | Fail err -> 
                config.LoggerN err.DebugInfo
                raise <| Util.AnalysisException $"Error duing DPA construction: %s{err.Info}"
                
    printfn $"printDPA: {dpa}"

    //generate good States
    let goodStates = ModelCounting.findNonEmptyStates sem dpa 
    printfn $"good States: {goodStates}"
    if goodStates.IsEmpty then  
        raise <| Util.AnalysisException "Good States are empty, no traces match this expression "
        exit 0
   
    if (sem = ModelCounting.Semantics.Existential) then
        generateExTraces aps learnOptions dpa goodStates
    else
        generateUniversalTraces aps learnOptions dpa goodStates rnd
    
let  generateLoopTraces aps ltl config (learnOptions: LearningOptions) (rnd: Random)=
    
    let dpa = 
            match FsOmegaLib.Operations.LTLConversion.convertLTLtoDPA false config.SolverConfiguration.MainPath config.SolverConfiguration.Ltl2tgbaPath ltl with 
            | Success x -> FsOmegaLib.DPA.DPA.fixAPs aps x 
            | Fail err -> 
                config.LoggerN err.DebugInfo
                raise <| Util.AnalysisException $"Error duing DPA construction: %s{err.Info}"
    let apsInt = [ 0.. List.length aps-1 ]          
    printfn $"printDPA: {dpa}"
    
    
    
    for i in 0 .. 10 do
        let finite, infinite = sampleLassoInDPA rnd 0 2 dpa
        printfn $"{gentraceFromTrace finite [0;1] rnd}"
        printfn $"{gentraceFromTrace infinite [0;1]rnd }"

    
    let rec trace number   =
            match number with
            | 0 -> []
            | n -> 
            let finite, infinite = sampleLassoInDPA rnd learnOptions.Length learnOptions.Length dpa
            {APs = dpa.APs; Trace =(gentraceFromTrace finite apsInt rnd); Loop=(gentraceFromTrace infinite apsInt rnd)}:: trace (n-1)
        
    trace learnOptions.NumberOfTraces
(* let computeCandidates (config : Configuration) (learnOption : LearningOptions) (traces : list<Trace<string>>) (sem : Semantics) = 

    let aps = 
        traces 
        |> List.map (fun x -> x.APs)
        |> List.concat
        |> List.distinct
    let aps =
        "a"::aps
        |> List.distinct *)

let buildSCCDPA (dpa: DPA<int,string>) sccList =
    let statesInSccList = 
        sccList|> List.toSeq |> Set.unionMany
    let oldStates = Set.difference dpa.States statesInSccList |> Set.map (fun x -> Original x)
    let newStates = [ for i in 1..sccList.Length -> New (i-1)] |> Set.ofList
    let listCSSNewState = [ 
        for i in 0..(sccList.Length-1) -> 
            //if ((sccList[i] |> Set.count)>1) then 
                //printfn $"dpa scc>0: {dpa}, scc: {sccList}"
            (New i, sccList[i])]
    let rec findOriginalState (original: int) (listCSSNewState: (DPAState * Set<int>) list) =
        match listCSSNewState with
        | [] -> failwith "initial not found"
        | (value,css)::xss ->
            if (Set.contains original css) then
                value
            else 
                findOriginalState original xss

    let rec findSCC sccList newValue = 
        match sccList with 
        | [] -> failwith "not found"
        | (New i, set_S)::xs -> if (i=newValue) then set_S else findSCC xs newValue
        | _ -> failwith "not reachable"
   

    let states = newStates + oldStates
    let color = 
        states |> Set.map (fun x -> 
            match x with 
            | Original x -> (Original x,dpa.Color[x])
            | New x -> 
                let scc = findSCC listCSSNewState x
                let colorSCC = scc  |> Set.map (fun x -> dpa.Color.[x])  |> Set.maxElement
                (New x,colorSCC))
            |> Set.toList
            |> Map.ofList
             
    let initial = 
        if (Set.contains (Original dpa.InitialState) oldStates)then
            Original dpa.InitialState 
        else 
            findOriginalState dpa.InitialState listCSSNewState
    
    let edges = 
        let NoSccStates =  Set.difference dpa.Skeleton.States statesInSccList
        let rec edgesBuild (edgeList: (DNF<int> * int) list) start =
            match edgeList with 
            | [] -> []
            | (dnf, endstate)::xs -> 
                if (Set.contains endstate NoSccStates) then
                    (dnf, Original endstate) :: edgesBuild xs start
                else 
                    let newState = findOriginalState endstate listCSSNewState 
                    let xsss = 
                        xs 
                        |> List.filter (fun(_, endstatee) -> not (Set.contains endstatee NoSccStates)) 
                        |> List.filter (fun (_, endstatee) -> (findOriginalState endstatee listCSSNewState) = newState) 
                    let edgesLeft =List.except xsss xs
                    let xsss =  
                        dnf::(xsss
                        |> List.map (fun (dnff,_) -> dnff) )
                    let rec constructDNF (dnflist: DNF<int> list)= match dnflist with | [] -> [] |x::xs -> x @ (constructDNF xs)
                    let dnff :DNF<int> = constructDNF xsss
                    //TODO: filter xs nach weiteren Edges fpr die gilt: findOriginalState ... ... = newState 
                    (* if (xsss.Length > 1) then
                        printfn $"xsss: {xsss}"
                        printfn $"dnf: {dnff}" *)
                    (* if (xsss.Length>1) then
                        printfn $"IMPORTANT" *)
                    (dnff,newState)::edgesBuild edgesLeft start

        let rec buildEdges (edgemap: Map<int, (DNF<int> *int) list>) states =
            match states with
            | [] -> []
            | x::xs -> 
                if (Set.contains x NoSccStates) then
                    let mapEntry = edgemap[x]
                    (Original x, edgesBuild mapEntry x):: buildEdges edgemap xs
                else
                    buildEdges edgemap xs

        let rec selfLoopsForSCC  newStates :((DPAState * ((DNF<int> * DPAState) list) ) list)=
            match newStates with
            | [] -> []
            | x::xs -> 
            (x,([[]],x)::[]) :: selfLoopsForSCC xs
        //
        
      
        Map.ofList (buildEdges dpa.Skeleton.Edges (dpa.Skeleton.States |> Set.toList) @ (selfLoopsForSCC (newStates |> Set.toList)) )

        
      
   
    let newdpa = {InitialState= initial; Color = color; Skeleton = {States =states; APs = dpa.Skeleton.APs; Edges =edges}}
    
    let newdpa = FsOmegaLib.DPA.DPA.convertStatesToInt(newdpa) |>  FsOmegaLib.DPA.DPA.fixAPs dpa.Skeleton.APs
    newdpa

let generateEdgeProbability (edges: Map<int,(DNF<int> * int) list>) states    (aps: String list): float list list=
    let aps = [ 0.. List.length aps-1 ]
    let rec powerset = function
                        | [] -> [[]]
                        | (x::xs) -> 
                            let xss = powerset xs 
                            List.map (fun xs' -> x::xs') xss @ xss
    let genFun list x =
                    if (List.exists (fun elem -> elem=x) list) then true else false
    let rec listOfFunction list =
                    match list with
                    | []-> []
                    | y::xs -> (genFun (y |> Set.toList)) ::(listOfFunction xs)
    let rec evalDNF list dnf= 
                    match list with
                    | []-> 0
                    | x::xs ->  if (FsOmegaLib.SAT.DNF.eval x dnf) then 1+ evalDNF xs dnf else evalDNF xs dnf

    let rec genRow (edges: Map<int,(DNF<int> * int) list>) (state: int) (totalStates: int list) =
        match totalStates with
        | []-> []
        | x::xs -> 
            let entry =  edges[state] |> List.exists (fun (_,endstate) -> endstate = x)
            if entry then                    
                let rec probability (dnf: DNF<int>) : float=
                    match dnf with
                    | [] -> 0.0
                    | _ -> 
                        let powersetList = powerset (aps) |> List.map Set.ofList
                        let functions = listOfFunction powersetList
                        //printfn $"dnf: {dnf}, prob: {float(evalDNF functions  dnf) / float(List.length functions)}"
                        float(evalDNF functions  dnf) / float(List.length functions)

                let (findEntry,_) = List.find (fun (_,endstate) -> endstate = x) edges[state]
                probability findEntry ::( genRow edges state xs)
            else  
            0.0::( genRow edges state xs)
        
    let rec genMatrix (edges: Map<int,(DNF<int> * int) list>) states totalStates = 
        match states with
        | [] -> []
        | state::states' -> (genRow edges state (totalStates |> List.sort)) :: (genMatrix edges states' totalStates)
    genMatrix edges states states







                
let generateMatrixP (edges: Map<int,(DNF<int> * int) list>) states  (apLength:int) (cssList:int list) (aps: String list): float list list=
    let aps = [ 0.. List.length aps-1 ]
    let rec powerset = 
                        function
                        | [] -> [[]]
                        | (x::xs) -> 
                            let xss = powerset xs 
                            List.map (fun xs' -> x::xs') xss @ xss
    let genFun list x =
                    if (List.exists (fun elem -> elem=x) list) then true else false
    let rec listOfFunction list =
                    match list with
                    | []-> []
                    | y::xs -> (genFun (y |> Set.toList)) ::(listOfFunction xs)
    let rec evalDNF list dnf= 
                    match list with
                    | []-> 0
                    | x::xs ->  if (FsOmegaLib.SAT.DNF.eval x dnf) then 1+ evalDNF xs dnf else evalDNF xs dnf

    let rec genRow (edges: Map<int,(DNF<int> * int) list>) (state: int) (totalStates: int list) =
        match totalStates with
        | []-> []
        | x::xs -> 
            let entry =  edges[state] |> List.exists (fun (dnf,endstate) -> endstate = x)
            if entry then
                                       
                let rec probability (dnf: DNF<int>)  (apLength: int): float=
                    match dnf with
                    | [] -> 0.0
                    | x::[] -> (1.0 / (float(2)**float(apLength - (apLength-x.Length)))) 
                    | _ -> 
                        let powersetList = powerset (aps) |> List.map Set.ofList
                        let functions = listOfFunction powersetList
                        //printfn $"dnf: {dnf}, prob: {float(evalDNF functions  dnf) / float(List.length functions)}"
                        float(evalDNF functions  dnf) / float(List.length functions)

                let (findEntry,endstate) = List.find (fun (_,endstate) -> endstate = x) edges[state]
                
                if (state=endstate) then 
                    if (List.exists (fun x -> x=state) cssList ) then 
                        probability findEntry apLength ::( genRow edges state xs)
                    else 
                        ((probability findEntry apLength)-1.0)::( genRow edges state xs)
                else  
                    (probability findEntry apLength)::( genRow edges state xs)
               
                
            else  
            (if (state=x) then -1.0 else 0.0 )::( genRow edges state xs)
        
    let rec genMatrix (edges: Map<int,(DNF<int> * int) list>) states totalStates = 
        match states with
        | [] -> []
        | state::states' -> (genRow edges state (totalStates |> List.sort)) :: (genMatrix edges states' totalStates)
    genMatrix edges states states

let genVector (length:int) (css:int) =
    let rec genVectorhelp (length:int) (css:int) =
        match length with
        | -1 -> []
        | n -> (if (css=n) then 1.0 else 0.0)::genVectorhelp (n-1) css
    (genVectorhelp length css ) |> List.rev
let rec generateCSSList (css: Set<int> list) =
    match css with
    | [] -> []
    | x::xs -> 
        if (x.Count = 1) then 
            ((x |> Set.toList) |> List.head) :: (generateCSSList xs)
            
        else 
            failwith "Set contains more than 1" 
            
let generateInitialVector (dpa: DPA<int,string>) =
    let states= dpa.States |> Set.toList |> List.sort |> List.map(fun x -> if (x=dpa.InitialState) then double(1.0) else double(0.0))
    [states]    
let computeNext (vector: Matrix<double>) (matrix: Matrix<double>) =
    vector.Multiply(matrix)
let rec stationaryDistribution (vector1: Matrix<double>) (vector2: Matrix<double>) (matrix: Matrix<double>) (length: int) (epsilon: float) =
    if ((vector1-vector2).L2Norm() < epsilon)then
        (true, vector2)
    else    
        if (length=0) then  
            (false, vector2)
        else stationaryDistribution vector2 (computeNext vector2 matrix) matrix (length-1) epsilon
let resultDensity (resultt: bool * Matrix<double>) (cssAccList: int list) =
    match resultt with
    | (true,v) -> 
        let rec computeDensityFromVector (resulttt: Matrix<double>) cssAccList =
            match cssAccList with
            | [] -> 0.0
            | x::xs -> resulttt.Column(x)[0] + ( computeDensityFromVector resulttt xs)
        

        computeDensityFromVector  v cssAccList
    | (false,_) -> -1.0

let rec computeLTLlatex ltl =
        match ltl with
        | Atom a -> $"{a}"
        | True -> "1"
        | False -> "0"
        | G e1 -> "(\\LTLglobally " + computeLTLlatex e1 + " )"
        | X e1 -> "(\\LTLnext " + computeLTLlatex e1 + " )"
        | F e1 -> "(\\LTLeventually " + computeLTLlatex e1 +  " )"
        | U(e1,e2) -> "(" + computeLTLlatex e1 + " \\LTLuntil " + computeLTLlatex e2 + ")"
        | W(e1,e2) -> "(" + computeLTLlatex e1 + " \\LTLweakuntil " + computeLTLlatex e2 + ")"
        | M(e1,e2) -> "(" + computeLTLlatex e1 + " M " + computeLTLlatex e2 + ")"
        | R(e1,e2) -> "(" + computeLTLlatex e1 + " R " + computeLTLlatex e2 + ")"
        | And(e1,e2) -> "(" + computeLTLlatex e1 + " \\land " + computeLTLlatex e2 + ")"
        | Or(e1,e2) -> "(" + computeLTLlatex e1 + " \\lor " + computeLTLlatex e2 + ")"
        | Implies(e1,e2) -> "(" + computeLTLlatex e1 + "\\rightarrow " + computeLTLlatex e2 + ")"
        | Equiv(e1,e2) -> "(" + computeLTLlatex e1 + " \\leftrightarrow " + computeLTLlatex e2 + ")"
        | Not e -> "( \\neg " + computeLTLlatex e + ")"
        | _ -> failwith $" outermost operator not found: {ltl}"

let rec computeLTLentry (scoreResults: ScoreResult list) (length: int) (current:int) =
    match length with
    | 0 -> ""
    | n ->    
        match       scoreResults with
        | [] -> failwith "not enough items"
        | x::xs -> 
        if (n=1) then 
            $"{current}. $" + computeLTLlatex x.Information.Formula + " $"+ computeLTLentry xs (n-1) (current+1) 
        else
            $"{current}. $"+  computeLTLlatex x.Information.Formula + " $ " + "\\\\"+ (computeLTLentry xs (n-1) (current+1))
let rec computeOverall  (scoreResults: ScoreResult list) (length: int)  =
    match length with 
    | 0 -> ""
    | n ->    
        match       scoreResults with
        | [] -> failwith "not enough items"
        | x::xs -> 
        if (n=1) then 
            $"%.2f{-Math.Log(x.OverallScore, 2.)}"
        else 
             $"%.2f{-Math.Log(x.OverallScore, 2.)} \\\\" + computeOverall xs (n-1)

let rec computeSimplicity  (scoreResults: ScoreResult list) (length: int)  =
    match length with 
    | 0 -> ""
    | n ->    
        match       scoreResults with
        | [] -> failwith "not enough items"
        | x::xs -> 
        if (n=1) then 
            if (-Math.Log(x.Simplicity, 2.)=0) then
                "0.00"
            else
                $"%.2f{-Math.Log(x.Simplicity, 2.)}"
        else 
            if (-Math.Log(x.Simplicity, 2.)=0) then
                "0.00 \\\\" + computeSimplicity xs (n-1)
            else
                $"%.2f{-Math.Log(x.Simplicity, 2.)} \\\\" + computeSimplicity xs (n-1)
let rec computeSpecificity  (scoreResults: ScoreResult list) (length: int)  =
    match length with 
    | 0 -> ""
    | n ->    
        match       scoreResults with
        | [] -> failwith "not enough items"
        | x::xs -> 
        if (n=1) then 
            if (-Math.Log(x.Specificity, 2.)=0) then
                "0.00"
            else $"%.2f{-Math.Log(x.Specificity, 2.)}"
        else 
            if (-Math.Log(x.Specificity, 2.)=0) then
                "0.00 \\\\" + computeSpecificity xs (n-1)
            else
                $"%.2f{-Math.Log(x.Specificity, 2.)} \\\\" + computeSpecificity xs (n-1)


let printLatexEntry (scoreResults: ScoreResult list) (length:int)=
    let ltlFormula =" \\makecell[l]{ " + (computeLTLentry scoreResults length 1 ) + "} &"
    let overallScore = " \\makecell[l]{ " + computeOverall scoreResults length + "} &"
    let simplicity = " \\makecell[l]{ " + computeSimplicity scoreResults length + "} &"
    let specificity   = " \\makecell[l]{ " + computeSpecificity scoreResults length + "} "
    ltlFormula + overallScore + simplicity + specificity

let densityOfLength length dpa =
    let rec densityForLength lengthLoop lengthPrefix dpa  =
        match lengthLoop with 
        | 0 -> 0
        | n -> (ModelCounting.countLassosOfGivenLength lengthPrefix lengthLoop dpa ) + densityForLength (n-1) (lengthPrefix+1) dpa 
    densityForLength length 0 dpa

let computeCandidates (config : Configuration) (learnOption : LearningOptions) (sem : SemanticsSetting) (aps) ltl= 
    let dpa = 
            match FsOmegaLib.Operations.LTLConversion.convertLTLtoDPA false config.SolverConfiguration.MainPath config.SolverConfiguration.Ltl2tgbaPath ltl with 
            | Success x -> x 
            | Fail err -> 
                config.LoggerN err.DebugInfo
                raise <| Util.AnalysisException $"Error duing DPA construction: %s{err.Info}"
    let rnd = System.Random(2)
    let finite, infinite = sampleLassoInDPA rnd 0 2 dpa
    printfn $"DPa: {dpa}"
    (* printfn $"Finite:{finite}, Infinite: {infinite}"
    for i in 0 .. 10 do
        printfn $"{gentraceFromTrace finite [0;1]}"
        printfn $"{gentraceFromTrace infinite [0;1]}"
    for i in 0 .. 100 do
        printfn $"Lassos: {sampleLassoInDPA rnd -1 2 dpa}" *)
    

    let css: Set<int> list = searchSCC dpa
    let accepting = acceptingCSS css dpa
(*     printfn $" {css[0] |> Set.count}"
    printfn $" {accepting[0] |> Set.count}"
    printfn $"DPA {dpa}" *)
    let initial = 1
    let states = [1;2;3;4;5;6;7;8] |> Set.ofList
    let color = Map.ofList [(1,2);(2,2);(3,2);(4,1);(5,2);(6,1);(7,1);(8,1)]
    let edges: Map<int,(DNF<int> * int) list> = Map.ofList [(6,[([[]],7)]); (7,[([[]],6)]);(1,[([[PL 0]],2);([[NL 0]],1)]); (2,[([[PL 0]],3);([[NL 0; PL 1]],5);([[NL 0; NL 1]],6)]); 
    
        (3,[([[NL 0]],3);([[PL 0]],4) ]);  (4,[([[NL 0]],3);([[PL 0]],8) ]); (8,[([[NL 0]],4);([[PL 0]],8) ]); (5,[([[NL 0]],6);([[PL 0]],1)])]
    let testDPA = {InitialState= initial; Color = color; Skeleton = {States =states; APs = ["a";"b"]; Edges =edges}}
    let testCss = searchSCC testDPA
    let accepting = acceptingCSS testCss testDPA

    
    printfn $"{testCss}"
    printfn $"{accepting}"
    let newdpa: DPA<int,string> = buildSCCDPA testDPA testCss
    printfn $"{newdpa}"
    let result =generateMatrixP newdpa.Skeleton.Edges (newdpa.Skeleton.States |> Set.toList) newdpa.APs.Length [3;4] newdpa.APs
    let result = matrix result
    printfn $"Result:"
    printfn $"Result: {result}"
    let vecotrr =genVector ((newdpa.Skeleton.States.Count)-1) 3
    let vectorr = vector vecotrr
    printfn $"{vectorr}"
    let solved =result.Solve(vectorr)
    printfn $"{solved}"
    printfn $"{solved[newdpa.InitialState]}"
    let vecotrr =vector (genVector ((newdpa.Skeleton.States.Count)-1) 4)
    let solved =result.Solve(vecotrr)
    printfn $"{solved}"
    printfn $"{solved[newdpa.InitialState]}"
  
   
    //let solved =result.Solve(vectorr)

    //let newdpa: DPA<int,string> = buildSCCDPA dpa css
        
   
    let rnd = System.Random(2)
    let infinite = (sem=Infinite)
    let traces = 
        if (sem=Infinite) then
            generateLoopTraces aps ltl config learnOption rnd
        else 
            if (sem=Existential) then
                generateTraces aps ltl config learnOption ModelCounting.Semantics.Existential rnd
            else 
                generateTraces aps ltl config learnOption ModelCounting.Semantics.Universal rnd
    for i in traces do
        printfn $"Trace: {i}"
    
    //exit 0
    //TODO: infinite traces
    

    config.LoggerN $"Generating formulas over APs %A{aps}"

    let candidates = 
        match learnOption.SamplingMethod with 
        | "spot" -> generateWeightedCandidatesBySpot config aps learnOption.NumberOfSamples learnOption.IncludeAllSubformulas true ltl
        //| "grammar" -> generateWeightedCandidatesByGrammar aps learnOption.NumberOfSamples 
        | "spotgen" -> generateWeightedCandidatesBySpot config aps learnOption.NumberOfSamples learnOption.IncludeAllSubformulas false ltl
        | o -> raise <| AnalysisException $"Non supported sampling option: %s{o}"

    config.LoggerN $"Generated %i{List.length candidates} candidate formulas"


    let candidates = (5 ,And (Atom "a",G (F (Atom "b"))))::candidates
    config.LoggerN $"Filter out candidates that do not hold on the given sample"
    let ltlAndSize = ( LTL.size ltl,ltl)
    let ltlAndSiz2 = (5 ,And (Atom "a",G (F (Atom "b"))))
    config.LoggerN $"{ltlAndSize}is in: %b{List.contains ltlAndSize candidates}"
    config.LoggerN $"{ltlAndSiz2}is in: %b{List.contains ltlAndSiz2 candidates}"
    
    (* let candidates = 
        candidates
        |> List.filter (fun (_, f) -> 
            traces 
            |> List.forall (fun trace -> 
                Trace.checkLtlOnTrace sem trace f
                )
            ) *)
    
    config.LoggerN $"{ltlAndSize}: traces fulfilled:  %b{List.contains ltlAndSize candidates}"
    config.LoggerN $"Left with %i{List.length candidates} candidate formulas"   
    



    //TODO: ab hier Fall unterscheidung
    // We assume all traces have the same length
    let traceLength = 
            traces.[0].Trace.Length
    let numberOfTotalModels = 
            (2.0 ** aps.Length) ** traceLength |> int
    let mutable results = []
    if (not infinite) then
        
        
        
        traces 
        |> List.iter (fun x -> 
            if x.Trace.Length <> traceLength then 
                raise <| AnalysisException "Traces are of differnt length")

        for (p, ltlFormula) in candidates do 
            //config.LoggerN "==========================================================="
            //config.LoggerN $"Candidate: %s{LTL.printInSpotFormat id ltl}"
            //config.LoggerN $"Weight: %f{p}"

            let dpa = 
                match FsOmegaLib.Operations.LTLConversion.convertLTLtoDPA false config.SolverConfiguration.MainPath config.SolverConfiguration.Ltl2tgbaPath ltlFormula with 
                | Success x -> FsOmegaLib.DPA.DPA.fixAPs aps x 
                | Fail err -> 
                    config.LoggerN err.DebugInfo
                    raise <| Util.AnalysisException $"Error duing DPA construction: %s{err.Info}"
            

            
            let semantics = 
                if (sem=Universal) then
                    ModelCounting.Semantics.Universal
                else
                    ModelCounting.Semantics.Existential
            let b = Trace.satisfiesTraces semantics dpa traces

            if ltlFormula=(ltl) then
                config.LoggerN $"{ltl} safisfies traces:  %b{b}"
                //exit 0

            
            if not b then 
                //printfn$"Does not satisfy traces: {ltlFormula}"
                //config.LoggerN "Does not satisfy traces"
                ()
            else 
                let numberOfModels = ModelCounting.countBoundedModels semantics traceLength dpa 
                // Account for all the APs not used in the DPA
                let missingApCount = aps.Length - dpa.APs.Length
                let additionalModels = (2.0 ** missingApCount) ** traceLength |> int

                let finalNumberOfModels = numberOfModels * additionalModels

                //let percentage = double(finalNumberOfModels) / double(numberOfTotalModels)
                //let nonSatPercentage = 1.0 - percentage
                //config.LoggerN $"%i{finalNumberOfModels}/%i{numberOfTotalModels}; %f{percentage}"

                results <- {Size= p; Formula = ltlFormula; Count = finalNumberOfModels} :: results

            //config.LoggerN "===========================================================\n"

        //config.LoggerN "\n\n\n"

    else
        for (p, ltlFormula) in candidates do 
            //config.LoggerN "==========================================================="
            //config.LoggerN $"Candidate: %s{LTL.printInSpotFormat id ltl}"
            //config.LoggerN $"Weight: %f{p}"

            let dpa = 
                match FsOmegaLib.Operations.LTLConversion.convertLTLtoDPA false config.SolverConfiguration.MainPath config.SolverConfiguration.Ltl2tgbaPath ltlFormula with 
                | Success x -> FsOmegaLib.DPA.DPA.fixAPs aps x 
                | Fail err -> 
                    config.LoggerN err.DebugInfo
                    raise <| Util.AnalysisException $"Error duing DPA construction: %s{err.Info}"
            let b = Trace.satisfiesLassoTraces dpa traces

            if ltlFormula=(ltl) then
                config.LoggerN $"{ltl} safisfies traces:  %b{b}"
                if b |> not then
                    failwith "traces does not fulfill formula"
                //exit 0

            
            if not b then 
                //printfn$"Does not satisfy traces: {ltlFormula}"
                //config.LoggerN "Does not satisfy traces"
                ()
            else 
                let css = searchSCC dpa
                let accepting = acceptingCSS css dpa
                let density=
                    //density of Length
                    double(densityOfLength 5 dpa) / (double(5)*((double(2)**double(dpa.APs |> List.length))**double(5)))
                    // if (accepting.IsEmpty) then 
                    //     0.0
                    // else 
                    //     //new density
                    //     let newdpa: DPA<int,string> = buildSCCDPA dpa css
                    //     let newcss: Set<int> list = searchSCC newdpa
                    //     let newacceptingCSS = acceptingCSS newcss newdpa
                    //     let acceptingcssList: int list = generateCSSList newacceptingCSS
                        
                    //     let pmatrix: Matrix<float>  =matrix (generateEdgeProbability  newdpa.Skeleton.Edges (newdpa.Skeleton.States |> Set.toList |> List.sort)  newdpa.APs)
                    //     let initvector: Matrix<float> = matrix (generateInitialVector  newdpa)
                    //     let next=computeNext initvector pmatrix
                    //     let stationaryDistribution = stationaryDistribution initvector next pmatrix 10000 (0.1**(64.0))
                    //     resultDensity stationaryDistribution acceptingcssList 
                       //finite density
                        


                        
                         

                                


                        

                //let percentage = double(finalNumberOfModels) / double(numberOfTotalModels)
                //let nonSatPercentage = 1.0 - percentage
                //config.LoggerN $"%i{finalNumberOfModels}/%i{numberOfTotalModels}; %f{percentage}"
                let density = Math.Round(density, 10, MidpointRounding.AwayFromZero)
                if (density = -1.0 |> not) then
                    results <- {Size= p; Formula = ltlFormula; Count = density} :: results
                else 
                    printfn $"density not converging for: {ltlFormula}"

   (*  printfn $"NUMBER OF TRACES: {results.Length}" *)
    (* for i in results do
        printfn $"{i.Formula}, {i.Count}" *)
    let shuffleR (r : Random) xs = xs |> Seq.sortBy (fun _ -> r.Next())
    let results = results |> shuffleR(new Random(0)) |> Seq.toList


    let sortedResults: ScoreResult list = 
        if (not infinite) then
            match learnOption.RankingMethod with 
            | "simple" -> rankResultsByNorm results numberOfTotalModels
            | "densityLight" -> densityLight results numberOfTotalModels
            | "densityLight2" -> densityLight2 results numberOfTotalModels
            | "densityLight3" -> densityLight3 results numberOfTotalModels
            | "regexScoreRegulateSizeDensity" ->regexScoreRegulateSizeDensity results numberOfTotalModels
            | "simpleRegex" -> regexScoreLight results
            | "regexScoreSameRange" -> regexScoreSameRange results
            | "regexScoreRegulateSize"-> regexScoreRegulateSize results
            | "regexScoreLinSize"-> regexScoreLinSize results
            | "densityLight0" -> densityLight0 results numberOfTotalModels
            //| "simpleNoRescale" -> rankResultsByNormWithoutRescale results
            | o -> raise <| AnalysisException $"Non supported ranking option: %s{o}"
        else 
            match learnOption.RankingMethod with
            | "densityScore" -> densityScore results
            | "densityScoreStrechedSize" -> densityScoreStrechedSize results
            |o -> raise <| AnalysisException $"Non supported ranking option: %s{o}"

    
    //for r in sortedResults do 
    printfn $"number of matching: {sortedResults.Length}"
    for r in sortedResults.[0..100] do 
        printfn $"%s{LTL.printInSpotFormat id r.Information.Formula}: ({r.Information.Size}, {r.Information.Count}, OverallScore: %.10f{-Math.Log(r.OverallScore, 2.)}, Simplicity: {-Math.Log(r.Simplicity, 2.)}, Specificity: {-Math.Log(r.Specificity, 2.)})\n"
    printfn $"{printLatexEntry  sortedResults 5}"
   // printLatexEntry  sortedResults 5
        //printfn $"%s{LTL.printInSpotFormat id r.Information.Formula}: ({r.Information.Size}, {r.Information.Count}, OverallScore: %.10f{r.OverallScore}, Simplicity: {r.Simplicity}, Specificity: {r.Specificity})\n"
//Prob = Simplicity, NonSat = Specificity
    ()