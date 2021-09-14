# eventb2javaincoq

Coq formalization of the soundness proof of the code generation carried out by the EventB2Java tool - the formalization includes a shallow embedding of the semantics of Event-B and JML in Coq. The main soundness proof condition in Coq states that any transition step in the semantics of JML in Coq is matched by a transition step in the semantics of the Evennt-B construct from which the JML construct was translated - The following paper describes the soundness proof: [Soundness Proof of EventB2Java]( https://ieeexplore.ieee.org/document/7781833) 
