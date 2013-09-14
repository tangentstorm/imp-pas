{$i test_lispmeta.def }
implementation uses imp;

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
    cx('(x y)', mCONS(x, mCONS( y, sNULL )));
  end;

procedure test_atomP;
  begin
    cx('T', mATOMP(Vx(1)));
    cx('T', mATOMP(sNULL));
    cx('T', mATOMP(x));
    cx('()', mATOMP(VL([1])));
    cx('()', mATOMP(L(x,y)));
  end;

procedure test_eqP;
  begin
    cx('T', mEQP(x, x));
    cx('()', mEQP(x, y));
    cx('()', mEQP(x, sNULL));
  end;

procedure test_car;
  begin
    cx('a', mCAR(L(a,b)));
    cx('x', mCAR(L(x)));
  end;

procedure test_cdr;
  begin
    cx('(b)', mCDR(L(a,b)));
    cx('()', mCDR(L(x)));
  end;

procedure test_cons;
  begin
    cx('(x)', mCONS(x, sNULL));
    cx('(y x)', mCONS(y, L(x)));
  end;

procedure test_mAPPQ;
  begin
    cx('((quote a) (quote b))', mAPPQ(L(a,b)));
  end;

procedure test_env;
  begin
    cx('((a x) (b y) (c z) (x 1) (y 2) (z 3))', env)
  end;


// check eval
procedure cev(s : string; x:TExpr);
  begin
    cx(s, mEVAL(x, env))
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

end.
