module RandomFormula 

open System


open FParsec

open FsOmegaLib.LTL

open Util
open Configuration

let private apParser = 
    pipe2 
        letter 
        (manyChars (letter <|> digit <|> pchar '_'))
        (fun x y -> string(x) + y)

let getRandomFormula (solverConfig : SolverConfiguration) (seed : int) (number : int) (aps : list<String>) (random: bool)=  
    let arg = 
        if random then
            [
                "--seed";
                string(seed);
                //"--tree-size=22..30";
                "--ltl-priorities \"xor=0, M=0, R=0\"";
                "-p";
                "-n" + string(number);
                aps |> Util.combineStringsWithSeperator " ";
            ]
            |> Util.combineStringsWithSeperator " "
        else
        //TODO
            " "

    let res = 
        if random then
            Util.SubprocessUtil.executeSubprocess solverConfig.RandltlPath arg
        else
        //TODO
            Util.SubprocessUtil.executeSubprocess solverConfig.GenltlPath arg

    assert(res.Stderr.Trim() = "")

    let out = res.Stdout
    
    let formulas = 
        out.Split ('\n')
        |> Array.toList
        |> List.map (fun x -> x.Trim())
        |> List.filter (fun x -> x <> "")
        |> List.map (fun x -> 
            match FsOmegaLib.LTL.Parser.parseLTL apParser x with 
            | Result.Ok y -> y 
            | Result.Error e -> failwith e
            )

    formulas