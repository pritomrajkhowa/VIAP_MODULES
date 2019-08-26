"""Most of these tests come from the examples in Bronstein's book."""
from sympy.integrals.risch import (DifferentialExtension, NonElementaryIntegral,
        derivation, risch_integrate)
from sympy.integrals.prde import (prde_normal_denom, prde_special_denom,
    prde_linear_constraints, constant_system, prde_spde, prde_no_cancel_b_large,
    prde_no_cancel_b_small, limited_integrate_reduce, limited_integrate,
    is_deriv_k, is_log_deriv_k_t_radical, parametric_log_deriv_heu,
    is_log_deriv_k_t_radical_in_field, param_poly_rischDE, param_rischDE,
    prde_cancel_liouvillian)

from sympy.polys.polymatrix import PolyMatrix as Matrix

from sympy import Poly, S, symbols, integrate, log, I, pi, exp
from sympy.abc import x, t, n, y

t0, t1, t2, t3, k = symbols('t:4 k')


def test_prde_normal_denom():
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(1 + t**2, t)]})
    fa = Poly(1, t)
    fd = Poly(x, t)
    G = [(Poly(t, t), Poly(1 + t**2, t)), (Poly(1, t), Poly(x + x*t**2, t))]
    assert prde_normal_denom(fa, fd, G, DE) == \
        (Poly(x, t), (Poly(1, t), Poly(1, t)), [(Poly(x*t, t),
         Poly(t**2 + 1, t)), (Poly(1, t), Poly(t**2 + 1, t))], Poly(1, t))
    G = [(Poly(t, t), Poly(t**2 + 2*t + 1, t)), (Poly(x*t, t),
        Poly(t**2 + 2*t + 1, t)), (Poly(x*t**2, t), Poly(t**2 + 2*t + 1, t))]
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(t, t)]})
    assert prde_normal_denom(Poly(x, t), Poly(1, t), G, DE) == \
        (Poly(t + 1, t), (Poly((-1 + x)*t + x, t), Poly(1, t)), [(Poly(t, t),
        Poly(1, t)), (Poly(x*t, t), Poly(1, t)), (Poly(x*t**2, t),
        Poly(1, t))], Poly(t + 1, t))


def test_prde_special_denom():
    a = Poly(t + 1, t)
    ba = Poly(t**2, t)
    bd = Poly(1, t)
    G = [(Poly(t, t), Poly(1, t)), (Poly(t**2, t), Poly(1, t)), (Poly(t**3, t), Poly(1, t))]
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(t, t)]})
    assert prde_special_denom(a, ba, bd, G, DE) == \
        (Poly(t + 1, t), Poly(t**2, t), [(Poly(t, t), Poly(1, t)),
        (Poly(t**2, t), Poly(1, t)), (Poly(t**3, t), Poly(1, t))], Poly(1, t))
    G = [(Poly(t, t), Poly(1, t)), (Poly(1, t), Poly(t, t))]
    assert prde_special_denom(Poly(1, t), Poly(t**2, t), Poly(1, t), G, DE) == \
        (Poly(1, t), Poly(t**2 - 1, t), [(Poly(t**2, t), Poly(1, t)),
        (Poly(1, t), Poly(1, t))], Poly(t, t))
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(-2*x*t0, t0)]})
    DE.decrement_level()
    G = [(Poly(t, t), Poly(t**2, t)), (Poly(2*t, t), Poly(t, t))]
    assert prde_special_denom(Poly(5*x*t + 1, t), Poly(t**2 + 2*x**3*t, t), Poly(t**3 + 2, t), G, DE) == \
        (Poly(5*x*t + 1, t), Poly(0, t), [(Poly(t, t), Poly(t**2, t)),
        (Poly(2*t, t), Poly(t, t))], Poly(1, x))
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly((t**2 + 1)*2*x, t)]})
    G = [(Poly(t + x, t), Poly(t*x, t)), (Poly(2*t, t), Poly(x**2, x))]
    assert prde_special_denom(Poly(5*x*t + 1, t), Poly(t**2 + 2*x**3*t, t), Poly(t**3, t), G, DE) == \
        (Poly(5*x*t + 1, t), Poly(0, t), [(Poly(t + x, t), Poly(x*t, t)),
        (Poly(2*t, t, x), Poly(x**2, t, x))], Poly(1, t))
    assert prde_special_denom(Poly(t + 1, t), Poly(t**2, t), Poly(t**3, t), G, DE) == \
        (Poly(t + 1, t), Poly(0, t), [(Poly(t + x, t), Poly(x*t, t)), (Poly(2*t, t, x),
        Poly(x**2, t, x))], Poly(1, t))


def test_prde_linear_constraints():
    DE = DifferentialExtension(extension={'D': [Poly(1, x)]})
    G = [(Poly(2*x**3 + 3*x + 1, x), Poly(x**2 - 1, x)), (Poly(1, x), Poly(x - 1, x)),
        (Poly(1, x), Poly(x + 1, x))]
    assert prde_linear_constraints(Poly(1, x), Poly(0, x), G, DE) == \
        ((Poly(2*x, x), Poly(0, x), Poly(0, x)), Matrix([[1, 1, -1], [5, 1, 1]]))
    G = [(Poly(t, t), Poly(1, t)), (Poly(t**2, t), Poly(1, t)), (Poly(t**3, t), Poly(1, t))]
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(t, t)]})
    assert prde_linear_constraints(Poly(t + 1, t), Poly(t**2, t), G, DE) == \
        ((Poly(t, t), Poly(t**2, t), Poly(t**3, t)), Matrix(0, 3, []))
    G = [(Poly(2*x, t), Poly(t, t)), (Poly(-x, t), Poly(t, t))]
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(1/x, t)]})
    prde_linear_constraints(Poly(1, t), Poly(0, t), G, DE) == \
        ((Poly(0, t), Poly(0, t)), Matrix([[2*x, -x]]))


def test_constant_system():
    A = Matrix([[-(x + 3)/(x - 1), (x + 1)/(x - 1), 1],
                [-x - 3, x + 1, x - 1],
                [2*(x + 3)/(x - 1), 0, 0]])
    u = Matrix([(x + 1)/(x - 1), x + 1, 0])
    DE = DifferentialExtension(extension={'D': [Poly(1, x)]})
    assert constant_system(A, u, DE) == \
        (Matrix([[1, 0, 0],
                 [0, 1, 0],
                 [0, 0, 0],
                 [0, 0, 1]]), Matrix([0, 1, 0, 0]))


def test_prde_spde():
    D = [Poly(x, t), Poly(-x*t, t)]
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(1/x, t)]})
    # TODO: when bound_degree() can handle this, test degree bound from that too
    assert prde_spde(Poly(t, t), Poly(-1/x, t), D, n, DE) == \
        (Poly(t, t), Poly(0, t), [Poly(2*x, t), Poly(-x, t)],
        [Poly(-x**2, t), Poly(0, t)], n - 1)


def test_prde_no_cancel():
    # b large
    DE = DifferentialExtension(extension={'D': [Poly(1, x)]})
    assert prde_no_cancel_b_large(Poly(1, x), [Poly(x**2, x), Poly(1, x)], 2, DE) == \
        ([Poly(x**2 - 2*x + 2, x), Poly(1, x)], Matrix([[1, 0, -1, 0],
                                                        [0, 1, 0, -1]]))
    assert prde_no_cancel_b_large(Poly(1, x), [Poly(x**3, x), Poly(1, x)], 3, DE) == \
        ([Poly(x**3 - 3*x**2 + 6*x - 6, x), Poly(1, x)], Matrix([[1, 0, -1, 0],
                                                                 [0, 1, 0, -1]]))
    assert prde_no_cancel_b_large(Poly(x, x), [Poly(x**2, x), Poly(1, x)], 1, DE) == \
        ([Poly(x, x, domain='ZZ'), Poly(0, x, domain='ZZ')], Matrix([[1, -1,  0,  0],
                                                                    [1,  0, -1,  0],
                                                                    [0,  1,  0, -1]]))
    # b small
    # XXX: Is there a better example of a monomial with D.degree() > 2?
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(t**3 + 1, t)]})

    # My original q was t**4 + t + 1, but this solution implies q == t**4
    # (c1 = 4), with some of the ci for the original q equal to 0.
    G = [Poly(t**6, t), Poly(x*t**5, t), Poly(t**3, t), Poly(x*t**2, t), Poly(1 + x, t)]
    assert prde_no_cancel_b_small(Poly(x*t, t), G, 4, DE) == \
        ([Poly(t**4/4 - x/12*t**3 + x**2/24*t**2 + (-S(11)/12 - x**3/24)*t + x/24, t),
        Poly(x/3*t**3 - x**2/6*t**2 + (-S(1)/3 + x**3/6)*t - x/6, t), Poly(t, t),
        Poly(0, t), Poly(0, t)], Matrix([[1, 0,      -1, 0, 0,  0,  0,  0,  0,  0],
                                         [0, 1, -S(1)/4, 0, 0,  0,  0,  0,  0,  0],
                                         [0, 0,       0, 0, 0,  0,  0,  0,  0,  0],
                                         [0, 0,       0, 1, 0,  0,  0,  0,  0,  0],
                                         [0, 0,       0, 0, 1,  0,  0,  0,  0,  0],
                                         [1, 0,       0, 0, 0, -1,  0,  0,  0,  0],
                                         [0, 1,       0, 0, 0,  0, -1,  0,  0,  0],
                                         [0, 0,       1, 0, 0,  0,  0, -1,  0,  0],
                                         [0, 0,       0, 1, 0,  0,  0,  0, -1,  0],
                                         [0, 0,       0, 0, 1,  0,  0,  0,  0, -1]]))

    # TODO: Add test for deg(b) <= 0 with b small
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(1 + t**2, t)]})
    b = Poly(-1/x**2, t, field=True)  # deg(b) == 0
    q = [Poly(x**i*t**j, t, field=True) for i in range(2) for j in range(3)]
    h, A = prde_no_cancel_b_small(b, q, 3, DE)
    V = A.nullspace()
    assert len(V) == 1
    assert V[0] == Matrix([-1/2, 0, 0, 1, 0, 0]*3)
    assert (Matrix([h])*V[0][6:, :])[0] == Poly(x**2/2, t, domain='ZZ(x)')
    assert (Matrix([q])*V[0][:6, :])[0] == Poly(x - 1/2, t, domain='QQ(x)')


def test_prde_cancel_liouvillian():
    ### 1. case == 'primitive'
    # used when integrating f = log(x) - log(x - 1)
    # Not taken from 'the' book
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(1/x, t)]})
    p0 = Poly(0, t, field=True)
    h, A = prde_cancel_liouvillian(Poly(-1/(x - 1), t), [Poly(-x + 1, t), Poly(1, t)], 1, DE)
    V = A.nullspace()
    h == [p0, p0, Poly((x - 1)*t, t), p0, p0, p0, p0, p0, p0, p0, Poly(x - 1, t), Poly(-x**2 + x, t), p0, p0, p0, p0]
    assert A.rank() == 16
    assert (Matrix([h])*V[0][:16, :]) == Matrix([[Poly(0, t, domain='QQ(x)')]])

    ### 2. case == 'exp'
    # used when integrating log(x/exp(x) + 1)
    # Not taken from book
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(-t, t)]})
    assert prde_cancel_liouvillian(Poly(0, t, domain='QQ[x]'), [Poly(1, t, domain='QQ(x)')], 0, DE) == \
            ([Poly(1, t, domain='QQ'), Poly(x, t)], Matrix([[-1, 0, 1]]))


def test_param_poly_rischDE():
    DE = DifferentialExtension(extension={'D': [Poly(1, x)]})
    a = Poly(x**2 - x, x, field=True)
    b = Poly(1, x, field=True)
    q = [Poly(x, x, field=True), Poly(x**2, x, field=True)]
    h, A = param_poly_rischDE(a, b, q, 3, DE)

    assert A.nullspace() == [Matrix([0, 1, 1, 1])]  # c1, c2, d1, d2
    # Solution of a*Dp + b*p = c1*q1 + c2*q2 = q2 = x**2
    # is d1*h1 + d2*h2 = h1 + h2 = x.
    assert h[0] + h[1] == Poly(x, x)
    # a*Dp + b*p = q1 = x has no solution.

    a = Poly(x**2 - x, x, field=True)
    b = Poly(x**2 - 5*x + 3, x, field=True)
    q = [Poly(1, x, field=True), Poly(x, x, field=True),
         Poly(x**2, x, field=True)]
    h, A = param_poly_rischDE(a, b, q, 3, DE)

    assert A.nullspace() == [Matrix([3, -5, 1, -5, 1, 1])]
    p = -5*h[0] + h[1] + h[2]  # Poly(1, x)
    assert a*derivation(p, DE) + b*p == Poly(x**2 - 5*x + 3, x)


def test_param_rischDE():
    DE = DifferentialExtension(extension={'D': [Poly(1, x)]})
    p1, px = Poly(1, x, field=True), Poly(x, x, field=True)
    G = [(p1, px), (p1, p1), (px, p1)]  # [1/x, 1, x]
    h, A = param_rischDE(-p1, Poly(x**2, x, field=True), G, DE)
    assert len(h) == 3
    p = [hi[0].as_expr()/hi[1].as_expr() for hi in h]
    V = A.nullspace()
    assert len(V) == 2
    assert V[0] == Matrix([-1, 1, 0, -1, 1, 0])
    y = -p[0] + p[1] + 0*p[2]  # x
    assert y.diff(x) - y/x**2 == 1 - 1/x  # Dy + f*y == -G0 + G1 + 0*G2

    # the below test computation takes place while computing the integral
    # of 'f = log(log(x + exp(x)))'
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(t, t)]})
    G = [(Poly(t + x, t, domain='ZZ(x)'), Poly(1, t, domain='QQ')), (Poly(0, t, domain='QQ'), Poly(1, t, domain='QQ'))]
    h, A = param_rischDE(Poly(-t - 1, t, field=True), Poly(t + x, t, field=True), G, DE)
    assert len(h) == 5
    p = [hi[0].as_expr()/hi[1].as_expr() for hi in h]
    V = A.nullspace()
    assert len(V) == 3
    assert V[0] == Matrix([0, 0, 0, 0, 1, 0, 0])
    y = 0*p[0] + 0*p[1] + 1*p[2] + 0*p[3] + 0*p[4]
    assert y.diff(t) - y/(t + x) == 0   # Dy + f*y = 0*G0 + 0*G1


def test_limited_integrate_reduce():
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(1/x, t)]})
    assert limited_integrate_reduce(Poly(x, t), Poly(t**2, t), [(Poly(x, t),
    Poly(t, t))], DE) == \
        (Poly(t, t), Poly(-1/x, t), Poly(t, t), 1, (Poly(x, t), Poly(1, t)),
        [(Poly(-x*t, t), Poly(1, t))])


def test_limited_integrate():
    DE = DifferentialExtension(extension={'D': [Poly(1, x)]})
    G = [(Poly(x, x), Poly(x + 1, x))]
    assert limited_integrate(Poly(-(1 + x + 5*x**2 - 3*x**3), x),
    Poly(1 - x - x**2 + x**3, x), G, DE) == \
        ((Poly(x**2 - x + 2, x), Poly(x - 1, x)), [2])
    G = [(Poly(1, x), Poly(x, x))]
    assert limited_integrate(Poly(5*x**2, x), Poly(3, x), G, DE) == \
        ((Poly(5*x**3/9, x), Poly(1, x)), [0])


def test_is_log_deriv_k_t_radical():
    DE = DifferentialExtension(extension={'D': [Poly(1, x)], 'exts': [None],
        'extargs': [None]})
    assert is_log_deriv_k_t_radical(Poly(2*x, x), Poly(1, x), DE) is None

    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(2*t1, t1), Poly(1/x, t2)],
        'exts': [None, 'exp', 'log'], 'extargs': [None, 2*x, x]})
    assert is_log_deriv_k_t_radical(Poly(x + t2/2, t2), Poly(1, t2), DE) == \
        ([(t1, 1), (x, 1)], t1*x, 2, 0)
    # TODO: Add more tests

    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(t0, t0), Poly(1/x, t)],
        'exts': [None, 'exp', 'log'], 'extargs': [None, x, x]})
    assert is_log_deriv_k_t_radical(Poly(x + t/2 + 3, t), Poly(1, t), DE) == \
        ([(t0, 2), (x, 1)], x*t0**2, 2, 3)


def test_is_deriv_k():
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(1/x, t1), Poly(1/(x + 1), t2)],
        'exts': [None, 'log', 'log'], 'extargs': [None, x, x + 1]})
    assert is_deriv_k(Poly(2*x**2 + 2*x, t2), Poly(1, t2), DE) == \
        ([(t1, 1), (t2, 1)], t1 + t2, 2)

    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(1/x, t1), Poly(t2, t2)],
        'exts': [None, 'log', 'exp'], 'extargs': [None, x, x]})
    assert is_deriv_k(Poly(x**2*t2**3, t2), Poly(1, t2), DE) == \
        ([(x, 3), (t1, 2)], 2*t1 + 3*x, 1)
    # TODO: Add more tests, including ones with exponentials

    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(2/x, t1)],
        'exts': [None, 'log'], 'extargs': [None, x**2]})
    assert is_deriv_k(Poly(x, t1), Poly(1, t1), DE) == \
        ([(t1, S(1)/2)], t1/2, 1)

    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(2/(1 + x), t0)],
        'exts': [None, 'log'], 'extargs': [None, x**2 + 2*x + 1]})
    assert is_deriv_k(Poly(1 + x, t0), Poly(1, t0), DE) == \
        ([(t0, S(1)/2)], t0/2, 1)

    # Issue 10798
    # DE = DifferentialExtension(log(1/x), x)
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(-1/x, t)],
        'exts': [None, 'log'], 'extargs': [None, 1/x]})
    assert is_deriv_k(Poly(1, t), Poly(x, t), DE) == ([(t, 1)], t, 1)


def test_is_log_deriv_k_t_radical_in_field():
    # NOTE: any potential constant factor in the second element of the result
    # doesn't matter, because it cancels in Da/a.
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(1/x, t)]})
    assert is_log_deriv_k_t_radical_in_field(Poly(5*t + 1, t), Poly(2*t*x, t), DE) == \
        (2, t*x**5)
    assert is_log_deriv_k_t_radical_in_field(Poly(2 + 3*t, t), Poly(5*x*t, t), DE) == \
        (5, x**3*t**2)

    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(-t/x**2, t)]})
    assert is_log_deriv_k_t_radical_in_field(Poly(-(1 + 2*t), t),
    Poly(2*x**2 + 2*x**2*t, t), DE) == \
        (2, t + t**2)
    assert is_log_deriv_k_t_radical_in_field(Poly(-1, t), Poly(x**2, t), DE) == \
        (1, t)
    assert is_log_deriv_k_t_radical_in_field(Poly(1, t), Poly(2*x**2, t), DE) == \
        (2, 1/t)


def test_parametric_log_deriv():
    DE = DifferentialExtension(extension={'D': [Poly(1, x), Poly(1/x, t)]})
    assert parametric_log_deriv_heu(Poly(5*t**2 + t - 6, t), Poly(2*x*t**2, t),
    Poly(-1, t), Poly(x*t**2, t), DE) == \
        (2, 6, t*x**5)
