module Grammar 

open System

open FsOmegaLib.LTL

type ASTGrammarCase<'T> = 
    {
        Weight : double 
        Arity : int
        Constructor : list<'T> -> 'T
    }

type ASTGrammar<'T> =
    {
        Cases: list<ASTGrammarCase<'T>>
    }

let rnd = new Random(0)


exception private ExploredToDeepException

let rec private sampleSingleFromGrammar (g : ASTGrammar<'T>) (depthBound : int) = 
    let weights = 
        g.Cases 
        |> List.map (fun x -> x.Weight)

    let cumWeights = 
        [0..g.Cases.Length - 1]
        |> List.map (fun x -> 
            g.Cases.[0..x]
            |> List.map (fun x -> x.Weight)
            |> List.sum
            )

    let weightSum = List.sum weights |> double

    let rec gen depth = 
        if depth > depthBound then 
            raise <| ExploredToDeepException

        let sample = rnd.NextDouble() * weightSum

        let caseIndex = 
            cumWeights
            |> List.findIndex (fun x -> sample <= x)

        let case = g.Cases.[caseIndex]

        let recRes = 
            [0..case.Arity - 1]
            |> List.map (fun _ -> gen (depth + 1))

        let prob = 
            recRes
            |> List.map fst 
            |> List.fold (*) (g.Cases.[caseIndex].Weight / weightSum)

        let term = 
            recRes
            |> List.map snd 
            |> case.Constructor

        prob, term
    
    try 
        gen 0 
        |> Some
    with 
    | ExploredToDeepException -> None


let sampleFromGrammar g (depthBound : int) n = 
    [0..n-1]
    |> List.map (fun _ -> sampleSingleFromGrammar g depthBound)
    |> List.choose id
    |> List.distinct

let exampleLTLGrammar (aps: list<'T>) = 

    let atomWeight = 0.7

    let atomCases = 
        aps 
        |> List.map (fun x -> 
            {
                // Until
                Weight = atomWeight / (aps |> List.length |> double)
                Arity = 0
                Constructor = fun _ -> Atom x
            }
        )

    {
        Cases = [
            {
                // True
                Weight = 0.1
                Arity = 0
                Constructor = fun _ -> True
            };
            {
                // False
                Weight = 0.1
                Arity = 0
                Constructor = fun _ -> False
            };
            {
                // And
                Weight = 0.3
                Arity = 2
                Constructor = 
                    function 
                    | [a; b] -> And(a, b)
                    | _ -> failwith ""
            };
            {
                // Or
                Weight = 0.3
                Arity = 2
                Constructor = 
                    function 
                    | [a; b] -> Or(a, b)
                    | _ -> failwith ""
            };
            {
                // Next
                Weight = 0.1
                Arity = 1
                Constructor = 
                    function 
                    | [a] -> X(a)
                    | _ -> failwith ""
            };
            {
                // Not
                Weight = 0.5
                Arity = 1
                Constructor = 
                    function 
                    | [a] -> X(a)
                    | _ -> failwith ""
            };
            {
                // G
                Weight = 0.5
                Arity = 1
                Constructor = 
                    function 
                    | [a] -> G a
                    | _ -> failwith ""
            };
            {
                // G
                Weight = 0.5
                Arity = 1
                Constructor = 
                    function 
                    | [a] -> F a
                    | _ -> failwith ""
            };
            {
                // Until
                Weight = 0.3
                Arity = 2
                Constructor = 
                    function 
                    | [a; b] -> U(a, b)
                    | _ -> failwith ""
            }
        ]
        @
        atomCases
    }
