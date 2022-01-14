sig Node {
    var adj : set Node
}

one sig Atual {
    var atual : one Node
}

fact {
    always all n : Node | n not in n.adj
    always all n1,n2 : Node | n1 in n2.adj implies n2 in n1.adj
}

fact Init{
    all n : Node | Node in n.*adj
    all n : Node | rem[#n.adj,2] = 0
}

pred elimAresta [n1 : Node, n2 : Node]{
    Atual.atual = n1
    
    n2 in n1.adj
    n1 in n2.^(adj') or #n1.adj=1

    Atual.atual' = n2
    n1.adj' = n1.adj - n2
    n2.adj' = n2.adj - n1

    
    all n : Node - n1 - n2 | n.adj' = n.adj
}

pred nop {
    adj' = adj
    Atual.atual' = Atual.atual
}

fact Traces {
    always{
        nop or 
            ( some n1,n2 : Node | elimAresta[n1,n2] )
    }
}

run Exemplo {} for 5 Node
