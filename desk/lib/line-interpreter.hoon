/+  *nock-compilation1
::
=*  stub  ~|(%stub !!)
|%
++  run
  |=  $:  args=(each (list *) *)  ::  optimized/pessimized call
          =bell
          scc=(set bell)
          rev=(jug bell bell)
          long-ska=_[=_code =_jets]:*long-ska
          scc-map=(map bell (set bell))
          jets-hot=(map ring need-ordered)
      ==
  =*  sam  +<
  ^-  (unit *)
  =/  straight
    ?:  -.args
      (~(got by (compile-scc scc rev long-ska scc-map jets-hot)) bell)
    -:(compile-unary bell scc rev long-ska scc-map jets-hot)
  ::
  =/  bob  (~(got by blocks.straight) 0w0)
  =/  regs=(map @uvre *)
    ?:  ?=(%| -.args)  [[0v0 p.args] ~ ~]
    =/  r=@uvre  0v0
    %-  malt
    |-  ^-  (list [@uvre *])
    ?~  p.args
      ?>  =(r n-args.straight)
      ~
    [[r i.p.args] $(p.args t.p.args, r +(r))]
  ::
  =|  params=(list *)
  |^  ^-  (unit *)
  =*  bob-loop  $
  =?  regs  .?(params)
    |-  ^+  regs
    ?~  params
      ?>  ?=(~ par.bob)
      regs
    ?>  ?=(^ par.bob)
    =.  regs  (put i.par.bob i.params)
    $(params t.params, par.bob t.par.bob)
  ::
  |-  ^-  (unit *)
  =*  body-loop  $
  ?:  ?=(^ body.bob)  body-loop(regs (exec-op i.body.bob), body.bob t.body.bob)
  =*  got-blocks  ~(got by blocks.straight)
  =/  fin  fin.bob
  |-  ^-  (unit *)
  =*  fin-retry  $  ::  no looping here
  ?-    -.fin
      %clq
    =/  j=jmp  ?^((get s.fin) z.fin o.fin)
    bob-loop(bob (got-blocks there.j), params (turn args.j get))
  ::
      %eqq
    =/  j=jmp  ?:(=((get l.fin) (get r.fin)) z.fin o.fin)
    bob-loop(bob (got-blocks there.j), params (turn args.j get))
  ::
      %brn
    =/  cond  (get s.fin)
    ?.  ?=(? cond)  ~
    =/  j=jmp  ?:(cond z.fin o.fin)
    bob-loop(bob (got-blocks there.j), params (turn args.j get))
  ::
      %hop
    bob-loop(bob (got-blocks there.t.fin), params (turn args.t.fin get))
  ::
      %jmp
    =/  sam-callee
      %=  sam
        args  &+(turn v.fin get)
        bell  a.fin
        scc   (~(gut by scc-map) a.fin [a.fin ~ ~])
      ==
    ::
    (run sam-callee)
  ::
      %jmf
    fin-retry(fin [%jmp a v]:fin)
  ::
      %jsp
    =/  sam-callee
      %=  sam
        args  |+(get s.fin)
        bell  a.fin
        scc   (~(gut by scc-map) a.fin [a.fin ~ ~])
      ==
    ::
    (run sam-callee)
  ::
      %jsf
    fin-retry(fin [%jsp a s]:fin)
  ::
      %don
    `(get s.fin)
  ::
      %bom
    ~
  ==
  ::
  ++  put
    |=  [r=@uvre n=*]
    ^+  regs
    (~(put by regs) r n)
  ::
  ++  get
    |=  r=@uvre
    ^-  *
    ?^  res=(~(get by regs) r)  u.res
    ~&  >>  [%missing-reg r `@ux`(mug bell)]
    %non-init-reg
    :: !!
  ::
  ++  exec-op
    |=  op=pole
    ^+  regs
    ?-    -.op
      %imm
    (put d.op n.op)
  ::
      %mov
    (put d.op (get s.op))
  ::
      %inc
    =/  a=*  (get s.op)
    ?^  a  ~
    (put d.op +(a))
  ::
      %con
    (put d.op [(get h.op) (get t.op)])
  ::
      %hed
    =/  a=*  (get s.op)
    =/  hed
      ?^  a  -.a
      ~&  >>  %missing-head
      %missing-head
    ::
    (put d.op hed)
  ::
      %tal
    =/  a=*  (get s.op)
    =/  tal
      ?^  a  +.a
      ~&  >>  %missing-tail
      %missing-tail
    ::
    (put d.op tal)
  ::
      %cel
    ?@  (get p.op)  ~
    regs
  ::
      %hsp
    :: ~&  [%hint n.op]
    regs
  ::
      %hse
    regs
  ::
      %hdp
    :: ~&  [%hint n.op]
    regs
  ::
      %hde
    regs
  ::
      %spy
    ~|  %scry-not-yet-implemented
    !!
  ::
      %nok
    ::  XX reenter analysis (unless jetted? and/or unless %virt?)
    ::
    =/  sub  (get u.op)
    =/  fol  (get f.op)
    ?~  res=(mole |.(.*(sub fol)))  ~
    (put d.op u.res)
  ::
      %cal
    =/  sam-callee
      %=  sam
        args  &+(turn v.op get)
        bell  a.op
        scc   (~(gut by scc-map) a.op [a.op ~ ~])
      ==
    ::
    ?~  res=(run sam-callee)  ~
    (put d.op u.res)
  ::
      %caf
    ::  no jets yet
    ::
    $(op [%cal a v d]:op)
  ::
      %cam
    ::  no memo yet
    ::
    $(op [%cal a v d]:op)
  ::
      %csl
    =/  sam-callee
      %=  sam
        args  |+(get s.op)
        bell  a.op
        scc   (~(gut by scc-map) a.op [a.op ~ ~])
      ==
    ::
    ?~  res=(run sam-callee)  ~
    (put d.op u.res)
  ::
      %csf
    $(op [%csl a s d]:op)
  ::
      %csm
    $(op [%csl a s d]:op)
    ==
  --
::
++  print-straight
  |=  [prefix=tape =straight]
  |^  ^-  tape
  =/  blocks=tape
    %-  zing
    %+  join  "\0a"
    %+  turn  ~(tap by blocks.straight)
    |=  [k=@uwoo v=blob]
    `tape`(weld prefix "{<k>}: {(p-blob v)}")
  ::
  %:  zing
    prefix
    (shape need.straight)
    "\0a"  prefix
    (scow %ud n-args.straight)
    "\0a"
    blocks
    ~
  ==
  ::
  ++  shape
    |=  need=need-ordered
    ^-  tape
    =;  axes=(list @)  <axes>
    =/  axe=@  1
    |-  ^-  (list @)
    ?-    -.need
        %none
      ~
    ::
        %this
      ~[axe]
    ::
        ^
      (weld $(need -.need, axe (peg axe 2)) $(need +.need, axe (peg axe 3)))
    ::
        %both
      :-  axe
      (weld $(need h.need, axe (peg axe 2)) $(need t.need, axe (peg axe 3)))
    ==
  ::
  ++  p-blob
    |=  b=blob
    ^-  tape
    %-  zing
    %+  join  "\0a"
    ^-  (list tape)
    =-  ?:  =(~ par.b)  -
        :_  -
        (zing prefix "params: " <par.b> ~)
    ::
    ^-  (list tape)
    :_  ~
    ^-  tape
    =/  body-ops=(list tape)  (turn body.b p-pole)
    %-  zing
    ?:  =(~ body-ops)
      (zing ~["\{"] ~[(p-termin fin.b) "}"] ~)
    (zing ~["\{"] (join " " body-ops) ~[" "] ~[(p-termin fin.b) "}"] ~)
  ::
  ++  p-pole
    |=  op=pole
    ^-  tape
    ?+    -.op  <op>
        %imm
      =/  n-tape=tape  <n.op>
      =?  n-tape  (gth (lent n-tape) 100)  "\{{(scag 100 n-tape)}...}"
      "[%imm n={n-tape} d={<d.op>}]"
    ::
        %hsp  <[%hsp n=n.op]>
        %hse  <[%hse n=n.op]>
        %hdp  <[%hdp n=n.op p=p.op]>
        %hde  <[%hde n=n.op p=p.op]>
    ::
        %cal
      <op(a `@ux`(mug a.op))>
    ::
        %caf
      <op(a `@ux`(mug a.op))>
    ::
        %cam
      <op(a `@ux`(mug a.op))>
    ::
        %csl
      <op(a `@ux`(mug a.op))>
    ::
        %csf
      <op(a `@ux`(mug a.op))>
    ::
        %csm
      <op(a `@ux`(mug a.op))>
    ==
  ::
  ++  p-termin
    |=  op=termin
    ^-  tape
    ?+    -.op  <op>
        %jmp
      <op(a `@ux`(mug a.op))>
    ::
        %jmf
      <op(a `@ux`(mug a.op))>
    ::
        %jsp
      <op(a `@ux`(mug a.op))>
    ::
        %jsf
      <op(a `@ux`(mug a.op))>
    ==
  --
--