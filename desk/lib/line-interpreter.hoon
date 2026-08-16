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
    ?~  p.args  ~
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
    ~&  >>  %missing-reg
    %non-init-reg
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
    ~&  [%hint n.op]
    regs
  ::
      %hse
    regs
  ::
      %hdp
    ~&  [%hint n.op]
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
    ::  XX reenter analysis
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
--