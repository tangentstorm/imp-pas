{$i test_lispmeta.def }
implementation uses uimp;

procedure cx( a : string; b : TExpr );
  begin
    chk.equal(a, ShowExpr( b ));
  end;

var a,b,c, x,y,z, env: TExpr;
procedure setup;
  begin
    a := Sym('a'); b := Sym('b'); c := Sym('c');
    x := Sym('x'); y := Sym('y'); z := Sym('z');
    env := L(L(a, x), L(b, y), L(c, z),
	     L(x, Vx(1)), L(y, Vx(2)), L(z, Vx(3)));
  end;

procedure test_vxvl;
  begin
    cx('(1 2)', VL([1,2]));
    cx('(a b c 1 2 3)', VL(['a','b','c',1,2,3]));
    cx('(x y)', ml.mCONS(x, ml.mCONS( y, sNULL )));
    cx('(cons a b)', L(sCons, a, b));
  end;

procedure test_atomP;
  begin
    cx('T', ml.mATOMP(Vx(1)));
    cx('T', ml.mATOMP(sNULL));
    cx('T', ml.mATOMP(x));
    cx('()', ml.mATOMP(VL([1])));
    cx('()', ml.mATOMP(L(x,y)));
  end;

procedure test_eqP;
  begin
    cx('T', ml.mEQP(x, x));
    cx('()', ml.mEQP(x, y));
    cx('()', ml.mEQP(x, sNULL));
  end;

procedure test_car;
  begin
    cx('a', ml.mCAR(L(a,b)));
    cx('x', ml.mCAR(L(x)));
  end;

procedure test_cdr;
  begin
    cx('(b)', ml.mCDR(L(a,b)));
    cx('()', ml.mCDR(L(x)));
  end;

procedure test_cons;
  begin
    cx('(x)', ml.mCONS(x, sNULL));
    cx('(y x)', ml.mCONS(y, L(x)));
  end;

procedure test_mAPPQ;
  begin
    cx('((quote a) (quote b))', ml.mAPPQ(L(a,b)));
  end;

procedure test_append;
  begin
    cx('(a b x y)', ml.mAPPEND(L(a,b), L(x,y)))
  end;

procedure test_env;
  begin
    cx('((a x) (b y) (c z) (x 1) (y 2) (z 3))', env)
  end;

// check eval
procedure cev(s : string; x:TExpr);
  begin
    cx(s, ml.mEVAL(x, ml.mAPPEND(env, mENV)))
  end;

procedure test_eval_atom;
  begin
    cev('1', x);
    cev('x', a);
  end;

procedure test_eval_quote;
  begin
    cev('x', q(x));
    cev('(cons a b)', q(L(sCons, a, b)));
  end;

procedure test_apply;
  begin
    cx('(a . b)', ml.mAPPLY(sCons, L(a, b), mENV));
    cx('(a b)', ml.mAPPLY(sCons, L(a, L(b)), mENV));
  end;

procedure test_arithmetic;
  begin
    cev('3', VL(['+', 1, 2 ]));
    cev('9', L(Vx('*'), Nx(3), VL(['+', 1, 2 ])));
  end;

procedure test_sym2chars;
  begin
    cev('(b a n a n a)', L(sSym2Chars, q(Sym('banana'))));
  end;

procedure test_chars2Sym;
  begin
    cev('banana', L(sChars2Sym, L(sSym2Chars, q(Sym('banana')))));
  end;

end.
