{$i test_imp.def }
implementation uses imp;

procedure cx( a : string; b : TExpr );
  begin
    chk.equal(a, ShowExpr( b ));
  end;

procedure test_vl;
  begin
    cx('(1 2)', VL([1,2]));
    cx('(1 2)', mCONS(Vx(1), mCONS( Vx(2), sNULL )));
  end;

procedure test_eval;
  begin
    cx('()', mEVAL( Sym('x'), sNULL ));
    cx('ok', mEVAL( Sym('x'), L(L( Sym('x'), Sym('ok') ))));
  end;

end.
