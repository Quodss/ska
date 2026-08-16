/+  *nock-compilation1
/+  li=line-interpreter
::
:-  %say  |=  *  :-  %noun
::
=/  subject=*  42
=/  formula=^  [4 0 1]
::
=/  [func=bell =long-ska]  (ska-poke [&+subject formula] *long-ska)
=/  [bell-graph=(jug bell bell) rev=(jug bell bell)]
  (simple-bell-graph-and-reversed graph.final.long-ska)
::
=/  sccs=(list (set bell))  (tarjan bell-graph)
=/  scc-map=(map bell (set bell))
  =|  out=(map bell (set bell))
  |-  ^+  out
  ?~  sccs  out
  %-  ~(rep in i.sccs)
  |=  [b=bell acc=_out]
  (~(put by acc) b i.sccs)
::
=/  scc-here=(set bell)  (~(gut by scc-map) func [func ~ ~])
(run:li |+subject func scc-here rev [code jets]:long-ska scc-map ~)