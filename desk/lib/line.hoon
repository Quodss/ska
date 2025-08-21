/-  *gene
=/  print-big-literals  |
::
|%
++  compile-all
  |=  lon=long
  |^  ^-  line
  =|  gen=line
  =.  gen
    %-  ~(rep by idxs.memo.lon)
    |=  [[k=@uxmemo v=meme] acc=_gen]
    ^+  acc
    =/  pog=prog
      :+  (compile code.v)
        less-code.v
      fol.v
    ::  
    =.  progs.acc  (~(put by progs.acc) (en-glob %memo k) pog)
    =.  fols.acc  (~(add ja fols.acc) fol.v pog)
    acc
  ::
  =.  gen
    %-  ~(rep by sites.arms.lon)
    |=  [[k=[@uvarm @uxsite] v=[less=sock fol=* =nomm]] acc=_gen]
    ^+  acc
    =/  pog=prog
      :+  (compile nomm.v)
        less.v
      fol.v
    ::
    =.  progs.acc  (~(put by progs.acc) (en-glob %site k) pog)
    =.  fols.acc  (~(add ja fols.acc) fol.v pog)
    acc
  ::
  gen
  ::
  ++  compile
    |=  n=nomm
    ^-  (list op)
    =|  out=(list op)
    ::  compilation flag
    ::
    =|  $=  flag
        $~  %tel
        $?  %tel    ::  tail position;
            %kip    ::  head, keep subject;
            %los    ::  head, lose subject.
        ==
    ::
    %-  flop
    |-  ^+  out
    ::  reversed program body
    ::
    ?^  -.n
      =?  out  ?=(%kip flag)  copy+out
      =.  out  $(n -.n, flag %kip)
      =.  out  swap+out
      =.  out  $(n +.n, flag %los)
      cons+out
    ?-    -.n
        %0
      ?:  =(0 p.n)  bail+out
      =?  out  ?=(%kip flag)  copy+out
      ?:  =(1 p.n)  out
      [axis+p.n out]
    ::
        %1
      =?  out  !?=(%kip flag)  lose+out
      [cnst+p.n out]
    ::
        %2
      ?~  site.n
        =?  out  ?=(%kip flag)  copy+out
        =.  out  $(n p.n, flag %kip)
        =.  out  swap+out
        =.  out  $(n q.n, flag %los)
        slow+out
      =.  out  $(n p.n)
      =/  idx=glob-atom  (en-glob site.n)
      =;  jet=(unit bell)
        =/  options  [f=flag j=jet]
        :_  out
        ?-  options
          [%tel ~]  jump+idx
          [%tel ^]  jumf+[idx u.j.options]
          [* ~]     call+idx
          [* ^]     calf+[idx u.j.options]
        ==
      ::
      =/  less=sock
        ?-    -.site.n
            %memo
          =/  =meme  (~(got by idxs.memo.lon) p.site.n)
          less-code.meme
        ::
            %site
          =/  site  (~(got by sites.arms.lon) p.site.n)
          less.site
        ==
      ::
      ~?  =(0xa6 idx)  n
      ~?  =(0xa6 idx)  less
      ?.  ?=([%0 @] q.n)
        ~?  =(0xa6 idx)  %weird-fol
        ~
      =/  ax=@  p.q.n
      =/  batt  (~(pull so less) 2)
      ?.  =(& cape.batt)
        ~?  =(0xa6 idx)  %unknown-batt
        ~
      ?@  data.batt
        ~?  =(0xa6 idx)  %atom-batt
        ~
      :: =/  dec-batt  [11 [1.835.100.275 1 6.514.020] 11 [1.851.876.717 [1 [1 1.717.658.988] 7 [0 1] 8 [1 1 100 101 99 114 101 109 101 110 116 45 117 110 100 101 114 102 108 111 119 0] 9 2 0 1] 0 1] 6 [5 [1 0] 0 6] [0 0] 8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]
      ~?  =(0xa6 idx)  data.batt
      ::  XX call.cole.lon instead
      ::
      =/  paths=(list path)  ~(tap in (~(get ju batt.jets.lon) data.batt))
      |-  ^-  (unit bell)
      =*  path-loop  $
      ?~  paths  ~
      =/  socks  ~(tap in (~(get ju core.jets.lon) i.paths))
      |-  ^-  (unit bell)
      =*  sock-loop  $
      ?~  socks  path-loop(paths t.paths)
      ?.  (~(huge so less) i.socks)  sock-loop(socks t.socks)
      `[i.paths ax]
    ::
        %3
      =.  out  $(n p.n)
      depf+out
    ::
        %4
      =.  out  $(n p.n)
      rise+out
    ::
        %5
      =?  out  ?=(%kip flag)  copy+out
      =.  out  $(n p.n, flag %kip)
      =.  out  swap+out
      =.  out  $(n q.n, flag %los)
      equi+out
    ::
        %6
      =/  yuh  $(n q.n, out ~)
      =/  nuh  $(n r.n, out ~)
      =.  yuh  [skip+(lent nuh) yuh]
      =.  out  $(n p.n, flag %kip)
      =.  out  [skim+(lent yuh) out]
      (zing nuh yuh out ~)
    ::
        %7
      =.  out  $(n p.n, flag ?:(?=(%tel flag) %los flag))
      $(n q.n, flag ?:(?=(%tel flag) %tel %los))
    ::
        %10
      ?:  =(0 p.p.n)  bail+out
      =?  out  ?=(%kip flag)  copy+out
      =.  out  $(n q.n, flag %kip)
      =.  out  swap+out
      =.  out  $(n q.p.n, flag %los)
      [edit+p.p.n out]
    ::
        %d11
      =.  out  $(n q.p.n, flag %kip)
      =.  out  lose+out
      $(n q.n)
    ::    
        %s11  $(n q.n)
        %12   ~|  %no-scry  !!
    ==
  --
::
++  tank-limit
  |=  [n=@ sam=*]
  ^-  @t
  =/  cod  (crip (zing (wash 0^80 >sam<)))
  ?:  (gth (met 3 cod) 5)  (scot %uw (mug sam))
  cod
::
++  render
  |=  ops=(list op)
  ^-  tank
  :+  %rose  [" " "\{" "}"]
  %+  turn  ops
  |=  o=op
  ^-  tank
  ?@  o  (scot %tas o)
  :+  %rose  [" " "[" "]"]
  :-  (scot %tas -.o)
  :_  ~
  ^-  tank
  ?-  -.o
    ?(%axis %skip %skim %edit)  (scot %ud +.o)
    %cnst  ?:(print-big-literals >p.o< (tank-limit 5 p.o))
    ?(%call %jump)  (scot %ux +.o)
    ?(%calf %jumf)  :+  %rose  [" " "" ""]
                    :~  (scot %ux p.o)
                        >q.o<
  ==                ==
::
++  exec
  |=  [sub=* fol=* lin=line]
  ^-  (unit *)
  =/  progs  (~(get ja fols.lin) fol)
  |-  ^-  (unit *)
  ?~  progs
    ~&  >>>  %exec-miss
    ~
  ?.  (~(huge so less.i.progs) &+sub)
    ~&  >>  %sock-nest
    $(progs t.progs)
  =/  prog  i.progs
  |-  ^-  (unit *)
  =*  prog-loop  $
  =/  stack=(list *)  ~[sub]
  =/  bod  body.prog
  %-  (slog (render bod) ~)
  |-  ^-  (unit *)
  :: ~&  stack
  ?:  =(~ bod)
    ?>  ?=([* ~] stack)
    `i.stack
  =^  o  bod  [i.-.bod t.+.bod]
  :: ~&  o
  ?-    o
      %slow
    ?>  ?=([* * *] stack)
    =/  fol  i.stack
    =/  sub  i.t.stack
    ?~  r=(mure |.(.*(sub fol)))  ~
    $(stack [u.r t.t.stack])
  ::
      %swap
    ?>  ?=([* * *] stack)
    $(stack [i.t.stack i.stack t.t.stack])
  ::
      %cons
    ?>  ?=([* * *] stack)
    $(stack [[i.t.stack i.stack] t.t.stack])
  ::
      %depf
    ?>  ?=([* *] stack)
    $(stack [.?(i.stack) t.stack])
  ::
      %rise
    ?>  ?=([* *] stack)
    ?^  i.stack  ~
    $(stack [+(i.stack) t.stack])
  ::
      %equi
    ?>  ?=([* * *] stack)
    $(stack [=(i.stack i.t.stack) t.t.stack])
  ::
      %bail  ~
      %copy
    ?>  ?=([* *] stack)
    $(stack [i.stack i.stack t.stack])
  ::
      %lose
    ?>  ?=([* *] stack)
    $(stack t.stack)
  ::
      [%axis p=@]
    ?>  ?=([* *] stack)
    ?~  r=(mure |.(.*(i.stack [0 p.o])))  ~
    $(stack [u.r t.stack])
  ::
      [%jump p=glob-atom]
    =/  new-bod  body:(~(got by progs.lin) p.o)
    %-  (slog (render new-bod) ~)
    $(bod new-bod)
  ::
      [%call p=glob-atom]
    ?>  ?=([* *] stack)
    =/  prod  prog-loop(sub i.stack, prog (~(got by progs.lin) p.o))
    :: ~&  %ret
    ?~  prod  ~
    $(stack [u.prod t.stack])
  ::  no jets for now
  ::
      [%jumf p=glob-atom q=*]
    $(bod [jump+p.o bod])
  ::
      [%calf p=glob-atom q=*]
    $(bod [call+p.o bod])
  ::
      [%cnst p=*]
    $(stack [p.o stack])
  ::
      [%skip p=@]
    $(bod (slag p.o bod))
  ::
      [%skim p=@]
    ?>  ?=([* *] stack)
    ?.  ?=(? i.stack)  ~
    =?  bod  !i.stack  (slag p.o bod)
    $(stack t.stack)
  ::
      [%edit p=@]
    ?>  ?=([* * *] stack)
    =/  don  i.stack
    =/  rec  i.t.stack
    ?~  r=(mure |.(.*([don rec] [%10 [p.o %0 2] %0 3])))  ~
    $(stack [u.r t.t.stack])
  ::
  ==
--