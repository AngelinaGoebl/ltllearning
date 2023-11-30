module GraphUtil 

open System.Collections.Generic

let shortestPathsBetweenAllPairs (nodes : seq<'T>) (forwardEdges: 'T -> seq<'E * 'T>) (includeZeroLengthPaths : bool) =
    let next = new Dictionary<_,_>(Seq.length nodes * Seq.length nodes)

    for n in nodes do 
        for (e, n') in forwardEdges n do 
            if Seq.contains n' nodes then 
                // In case there are multiple edges we just take the first (has no impact as the length is the same)
                if next.ContainsKey (n, n') |> not then 
                    next.Add((n, n'), ([e],[n; n']))

        if includeZeroLengthPaths then 
            next.Remove((n, n)) |> ignore
            next.Add((n, n), ([], [n]))

    for k in nodes do 
        for i in nodes do 
            for j in nodes do 
                if next.ContainsKey (i, k) && next.ContainsKey (k, j) then 
                    if next.ContainsKey (i, j) |> not || (next.[i, j] |> fst |> List.length > (next.[i, k] |> fst |> List.length) + (next.[k, j] |> fst |> List.length) + 1) then 
                        next.Remove((i,j)) |> ignore
                        next.Add((i, j), (fst next.[i, k] @ fst next.[k, j], snd next.[i, k] @ (next.[k, j] |> snd |> List.tail) ) )

    next

