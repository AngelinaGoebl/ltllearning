module Program 


open System
open System.Collections.Generic

open FParsec
open FsOmegaLib.SAT
open FsOmegaLib.LTL
open FsOmegaLib.DPA

open FsOmegaLib.Operations
open GraphUtil

open Util
open Configuration
open Learn
open RandomFormula
open Trace





let private apParser = 
    pipe2 
        letter 
        (manyChars (letter <|> digit <|> pchar '_'))
        (fun x y -> string(x) + y)

let test (config: Configuration) = 

    let ltl = LTL.F (Atom "a")

    let aps = ["a"; "b"]

    let dpa = 
        match FsOmegaLib.Operations.LTLConversion.convertLTLtoDPA false config.SolverConfiguration.MainPath config.SolverConfiguration.Ltl2tgbaPath ltl with 
        | Success x -> x 
        | Fail err -> raise <| Util.AnalysisException $"Error duing DPA construction: %s{err.Info}"

    let traceLength = 5

    let c = ModelCounting.countBoundedModels (ModelCounting.Semantics.Existential) traceLength dpa 

    let a = (2.0 ** aps.Length) ** traceLength |> int

    let r = double(c) / double(a)

    printfn $"%i{c}/ %i{a}"
    printfn $"%f{r}"



[<EntryPoint>]
let main args = 

    let config = 
        {
            SolverConfiguration = Configuration.getConfig()
            Logger = fun s -> printf $"%s{s}"
        }

    let learnOptions = 
        {
            LearningOptions.RankingMethod = "regexScoreRegulateSize"
            SamplingMethod = "spot"
            NumberOfSamples = 5000
            IncludeAllSubformulas = true
            Length = 10
            NumberOfTraces = 50
            

        }
        


    //test config

    let tracePath = args.[0]

    let tracesContent = 
        try 
            IO.File.ReadAllText tracePath
        with 
        | _ -> raise <| AnalysisException $"Could not open path %s{tracePath}"
    
    
    let splitted =  List.ofSeq(tracesContent.Split([|'\n'|]))  
    printfn $"{splitted}"
    let ltlstring = splitted[0]
    let aps = List.ofSeq(splitted[1].Split([|';'|]))
    printfn $"{ltlstring} , {aps}"
    
    (* let traces = 
        match Trace.Parser.parseTraces tracesContent with 
        | Result.Ok x -> x 
        | Result.Error err1 -> 
            // Try parsing it as a JSON
            match Trace.Parser.getTracesFromJsonString tracesContent with 
            | Result.Ok x -> x 
            | Result.Error err2 -> 
                raise <| AnalysisException $"Could not parse traces in either custom format or JSON: \n %s{err1}\n %s{err2}" *)
        
    
    //parse LTL Formula   
    let ltl =
        match FsOmegaLib.LTL.Parser.parseLTL apParser ltlstring with 
            | Result.Ok y -> y
            | Result.Error e -> raise <| AnalysisException $"Could not parse {e}"
    printfn $"{ltl}"
   

    //----------
    
    

        
        


    Learn.computeCandidates config learnOptions  (Learn.SemanticsSetting.Existential) aps ltl
        
    0
