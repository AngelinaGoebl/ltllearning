module Util 

open System

exception AnalysisException of string

let rec computeBooleanPowerSet n =
    if n = 0 then
        Seq.singleton []
    else
        let r = computeBooleanPowerSet (n-1)
        Seq.append (Seq.map (fun x -> true::x) r) (Seq.map (fun x -> false::x) r)
        
let rec combineStringsWithSeperator (s: string) (l: list<string>) = 
    match l with 
    | [] -> ""
    | [x] -> x
    | x::y::xs -> 
        x + s + combineStringsWithSeperator s (y::xs)


module SubprocessUtil = 

    type SubprocessResult = 
        {
            Stdout : String 
            Stderr : String 
            ExitCode : int
        }

    let executeSubprocess (cmd: string) (arg: string) = 
        let psi =
            System.Diagnostics.ProcessStartInfo(cmd, arg)

        psi.UseShellExecute <- false
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        psi.CreateNoWindow <- true
        let p = System.Diagnostics.Process.Start(psi)
        let output = System.Text.StringBuilder()
        let error = System.Text.StringBuilder()
        p.OutputDataReceived.Add(fun args -> output.Append(args.Data + "\n") |> ignore)
        p.ErrorDataReceived.Add(fun args -> error.Append(args.Data + "\n") |> ignore)
        p.BeginErrorReadLine()
        p.BeginOutputReadLine()
        p.WaitForExit()

        {
            SubprocessResult.Stdout = output.ToString();
            Stderr = error.ToString()
            ExitCode = p.ExitCode
        }
            
