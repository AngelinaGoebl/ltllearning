module Configuration


open System
open System.IO

open Util
open FsOmegaLib.JSON 


type SolverConfiguration = 
    {
        MainPath : String
        AutfiltPath: String
        Ltl2tgbaPath: String
        RandltlPath: String
        GenltlPath: String
    }

let private parseConfigFile (s : string) =
    match FsOmegaLib.JSON.Parser.parseJsonString s with 
    | Result.Error err -> raise <| AnalysisException $"Could not parse config file: %s{err}"
    | Result.Ok x -> 
        let autfiltPath = 
            try 
                x 
                |> JSON.lookup "autfilt" 
                |> JSON.getString
            with 
            | JsonError -> raise <| AnalysisException $"autfilt path not given"

        let ltl2tgbaPath = 
            try 
                x 
                |> JSON.lookup "ltl2tgba" 
                |> JSON.getString
            with 
            | JsonError -> raise <| AnalysisException $"ltl2tgba path not given"

        let randltlPath = 
            try 
                x 
                |> JSON.lookup "randltl" 
                |> JSON.getString
            with 
            | JsonError -> raise <| AnalysisException $"randltl path not given"

        let genltlPath = 
            try 
                x 
                |> JSON.lookup "genltl" 
                |> JSON.getString
            with 
            | JsonError -> raise <| AnalysisException $"genltl path not given"
        
        {
            MainPath = "./"
            AutfiltPath = autfiltPath
            Ltl2tgbaPath = ltl2tgbaPath
            RandltlPath = randltlPath
            GenltlPath = genltlPath
        }

let getConfig() = 
    // By convention the paths.json file is located in the same directory as the HyPA executable
    let configPath = 
        System.IO.Path.Join [|System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location); "paths.json"|]
                     
    // Check if the path to the config file is valid , i.e., the file exists
    if System.IO.FileInfo(configPath).Exists |> not then 
        raise <| AnalysisException "The paths.json file does not exist in the same directory as the executable"            
    
    // Parse the config File
    let configContent = 
        try
            File.ReadAllText configPath
        with 
            | _ -> 
                raise <| AnalysisException "Could not open paths.json file"

    let solverConfig = parseConfigFile configContent
 
    if System.IO.FileInfo(solverConfig.AutfiltPath).Exists |> not then 
        raise <| AnalysisException "The given path to the spot's autfilt is incorrect"

    if System.IO.FileInfo(solverConfig.Ltl2tgbaPath).Exists |> not then 
        raise <| AnalysisException "The given path to the spot's ltl2tgba is incorrect"

    if System.IO.FileInfo(solverConfig.RandltlPath).Exists |> not then 
        raise <| AnalysisException "The given path to the spot's randltl is incorrect"
        
    if System.IO.FileInfo(solverConfig.GenltlPath).Exists |> not then 
        raise <| AnalysisException "The given path to the spot's genltl is incorrect"

    solverConfig

type Configuration = 
    {
        SolverConfiguration: SolverConfiguration
        Logger : String -> unit
    }

    member this.LoggerN s = this.Logger (s + "\n")
