/+  *nock-compilation1
/+  li=line-interpreter
/+  hoot-zpdt
::
:-  %say  |=  *
::
=/  subject  [- 42 +>]:dec:hoot-zpdt
:: =/  formula=^  [%8 [%1 0] %8 [%1 %6 [%5 [%0 7] %4 %0 6] [%0 6] %9 2 [%0 2] [%4 %0 6] %0 7] %9 2 %0 1]
=/  formula=^
  ;;  ^
  -:dec:hoot-zpdt
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
  =.  out
    %-  ~(rep in i.sccs)
    |=  [b=bell acc=_out]
    (~(put by acc) b i.sccs)
  ::
  $(sccs t.sccs)
::
=/  scc-here=(set bell)  (~(gut by scc-map) func [func ~ ~])
?:  |
  noun+(run:li &+~[42] func scc-here rev [code jets]:long-ska scc-map ~)
=/  all-straights=(map bell straight)
  %-  ~(rep by scc-map)
  |=  [[k=* v=(set bell)] acc=(map bell straight)]
  (~(uni by acc) (compile-scc v rev [code jets]:long-ska scc-map ~))
::
:-  %tang
%-  flop  %-  to-wain:format  %-  crip
^-  tape
%-  zing
^-  (list tape)
%+  turn  ~(tap by all-straights)
|=  [k=bell v=straight]
"{<`@ux`(mug k)>}:\0a{(print-straight:li "  " v)}\0a"