
"""
A valid inequality for the product of two complex variables with magnitude and
angle difference bounds.

In the literature this constraints are called the Lifted Nonlinear Cuts (LNCs).

@misc{1512.04644,
    Author = {Carleton Coffrin and Hassan Hijazi and Pascal Van Hentenryck},
    Title = {Strengthening the SDP Relaxation of AC Power Flows with Convex
        Envelopes, Bound Tightening, and Lifted Nonlinear Cuts},
    Year = {2015},
    Eprint = {arXiv:1512.04644},
}
"""
function cut_complex_product_and_angle_difference(m, wf, wt, wr, wi, angmin, angmax)
    @assert angmin >= -pi/2 && angmin <= pi/2
    @assert angmax >= -pi/2 && angmax <= pi/2
    @assert angmin < angmax

    wf_lb, wf_ub = InfrastructureModels.variable_domain(wf)
    wt_lb, wt_ub = InfrastructureModels.variable_domain(wt)

    vf_lb, vf_ub = sqrt(wf_lb), sqrt(wf_ub)
    vt_lb, vt_ub = sqrt(wt_lb), sqrt(wt_ub)
    td_ub = angmax
    td_lb = angmin

    phi = (td_ub + td_lb)/2
    d   = (td_ub - td_lb)/2

    sf = vf_lb + vf_ub
    st = vt_lb + vt_ub

    JuMP.@constraint(m, sf*st*(cos(phi)*wr + sin(phi)*wi) - vt_ub*cos(d)*st*wf - vf_ub*cos(d)*sf*wt >=  vf_ub*vt_ub*cos(d)*(vf_lb*vt_lb - vf_ub*vt_ub))
    JuMP.@constraint(m, sf*st*(cos(phi)*wr + sin(phi)*wi) - vt_lb*cos(d)*st*wf - vf_lb*cos(d)*sf*wt >= -vf_lb*vt_lb*cos(d)*(vf_lb*vt_lb - vf_ub*vt_ub))
end


"""
A valid inequality for when the same product of two variables occurs in two
different higher order products (e.g. trilinear terms).

@misc{1809.04565,
    Author = {Kaarthik Sundar and Harsha Nagarajan and Sidhant Misra and
        Mowen Lu and Carleton Coffrin and Russell Bent},
    Title = {Optimization-Based Bound Tightening using a Strengthened
        QC-Relaxation of the Optimal Power Flow Problem},
    Year = {2018},
    Eprint = {arXiv:1809.04565},
}
"""
function cut_product_replicates(m, x, y, lambda_a, lambda_b)
    x_ub = JuMP.upper_bound(x)
    x_lb = JuMP.lower_bound(x)
    y_ub = JuMP.upper_bound(y)
    y_lb = JuMP.lower_bound(y)

    @assert length(lambda_a) == 8
    @assert length(lambda_b) == 8

    val = [x_lb * y_lb
           x_lb * y_lb
           x_lb * y_ub
           x_lb * y_ub
           x_ub * y_lb
           x_ub * y_lb
           x_ub * y_ub
           x_ub * y_ub]

    JuMP.@constraint(m, sum(lambda_a[i]*val[i] - lambda_b[i]*val[i] for i in 1:8) == 0)
end


"general relaxation of a sine term, in -pi/2 to pi/2"
function relaxation_sin(m, x, y)
    lb, ub = InfrastructureModels.variable_domain(x)
    @assert lb >= -pi/2 && ub <= pi/2

    max_ad = max(abs(lb),abs(ub))

    if lb < 0 && ub > 0
        JuMP.@constraint(m, y <= cos(max_ad/2)*(x - max_ad/2) + sin(max_ad/2))
        JuMP.@constraint(m, y >= cos(max_ad/2)*(x + max_ad/2) - sin(max_ad/2))
    end
    if ub <= 0
        JuMP.@constraint(m, y <= (sin(lb) - sin(ub))/(lb-ub)*(x - lb) + sin(lb))
        JuMP.@constraint(m, y >= cos(max_ad/2)*(x + max_ad/2) - sin(max_ad/2))
    end
    if lb >= 0
        JuMP.@constraint(m, y <= cos(max_ad/2)*(x - max_ad/2) + sin(max_ad/2))
        JuMP.@constraint(m, y >= (sin(lb) - sin(ub))/(lb-ub)*(x - lb) + sin(lb))
    end
end


"general relaxation of a cosine term, in -pi/2 to pi/2"
function relaxation_cos(m, x, y)
    lb, ub = InfrastructureModels.variable_domain(x)
    @assert lb >= -pi/2 && ub <= pi/2

    max_ad = max(abs(lb),abs(ub))

    JuMP.@constraint(m, y <= 1 - (1-cos(max_ad))/(max_ad*max_ad)*(x^2))
    JuMP.@constraint(m, y >= (cos(lb) - cos(ub))/(lb-ub)*(x - lb) + cos(lb))
end


"general relaxation of a sine term, in -pi/2 to pi/2"
function relaxation_sin_on_off(m, x, y, z, M_x)
    lb, ub = InfrastructureModels.variable_domain(x)
    @assert lb >= -pi/2 && ub <= pi/2

    max_ad = max(abs(lb),abs(ub))

    JuMP.@constraint(m, y <= z*sin(ub))
    JuMP.@constraint(m, y >= z*sin(lb))

    JuMP.@constraint(m,  y - cos(max_ad/2)*(x) <= z*(sin(max_ad/2) - cos(max_ad/2)*max_ad/2) + (1-z)*(cos(max_ad/2)*M_x))
    JuMP.@constraint(m, -y + cos(max_ad/2)*(x) <= z*(sin(max_ad/2) + cos(max_ad/2)*max_ad/2) + (1-z)*(cos(max_ad/2)*M_x))

    JuMP.@constraint(m, y <= z*(sin(max_ad/2) + cos(max_ad/2)*max_ad/2))
    JuMP.@constraint(m, -y <= z*(sin(max_ad/2) + cos(max_ad/2)*max_ad/2))

    JuMP.@constraint(m, cos(max_ad/2)*x <= z*(sin(max_ad/2) - cos(max_ad/2)*max_ad/2 + sin(max_ad)) + (1-z)*(cos(max_ad/2)*M_x))
    JuMP.@constraint(m, -cos(max_ad/2)*x <= z*(sin(max_ad/2) - cos(max_ad/2)*max_ad/2 + sin(max_ad)) + (1-z)*(cos(max_ad/2)*M_x))
end


"general relaxation of a cosine term, in -pi/2 to pi/2"
function relaxation_cos_on_off(m, x, y, z, M_x)
    lb, ub = InfrastructureModels.variable_domain(x)
    @assert lb >= -pi/2 && ub <= pi/2

    max_ad = max(abs(lb),abs(ub))

    JuMP.@constraint(m, y <= z)
    JuMP.@constraint(m, y >= z*cos(max_ad))
    # can this be integrated?
    #JuMP.@constraint(m, y >= (cos(lb) - cos(ub))/(lb-ub)*(x - lb) + cos(lb))

    JuMP.@constraint(m, y <= z - (1-cos(max_ad))/(max_ad^2)*(x^2) + (1-z)*((1-cos(max_ad))/(max_ad^2)*(M_x^2)))
end

"""
Kim Kojima Yamashita type-1 relaxation in conic form
```
(c^H.a)^H (c^H.a) <= alpha *((c.c^h)*A)
```
"""
function sdp_to_soc_kim_kojima_conic(m, Ar, Ai, ar, ai, alphar, cr, ci; tol=1e-8)
    @assert size(Ar) == size(Ai)
    @assert size(ar) == size(ai)

    @assert size(Ar)[1] == size(ar)[1]

    cr[abs.(cr).<=tol] .=0
    ci[abs.(ci).<=tol] .=0

    c = cr+im*ci
    C = c*c'
    Cr = real(C)
    Ci = imag(C)
    Cr[abs.(Cr).<=tol] .=0
    Ci[abs.(Ci).<=tol] .=0

    @assert size(Cr) == size(Ar)

    rhs_1 = alphar
    rhs_2 = sum(Cr.*Ar) + sum(Ci.*Ai)

    lhs_re = cr'* ar + ci'* ai
    lhs_im = cr'* ai - ci'* ar

    JuMP.@constraint(m, rhs_2 >= 0)
    JuMP.@constraint(m, [rhs_1+rhs_2;
                         rhs_1-rhs_2;
                         2*lhs_re;
                         2*lhs_im] in JuMP.SecondOrderCone())

end


"""
Kim Kojima Yamashita type-1 relaxation in conic form
```
(c^H.a)^H (c^H.a) <= alpha *((c.c^h)*A)
```
"""
function sdp_to_soc_kim_kojima(m, Ar, Ai, ar, ai, alphar, cr, ci; tol=1e-8)
    @assert size(Ar) == size(Ai)
    @assert size(ar) == size(ai)

    @assert size(Ar)[1] == size(ar)[1]

    cr[abs.(cr).<=tol] .=0
    ci[abs.(ci).<=tol] .=0

    c = cr+im*ci
    C = c*c'
    Cr = real(C)
    Ci = imag(C)
    Cr[abs.(Cr).<=tol] .=0
    Ci[abs.(Ci).<=tol] .=0

    @assert size(Cr) == size(Ar)

    rhs_1 = alphar
    rhs_2 = sum(Cr.*Ar) + sum(Ci.*Ai)

    lhs_re = cr'* ar + ci'* ai
    lhs_im = cr'* ai - ci'* ar

    JuMP.@constraint(m, rhs_2 >= 0)
    JuMP.@constraint(m, (rhs_1+rhs_2)^2 >=
                         (rhs_1-rhs_2)^2 + (2*lhs_re)^2 + (2*lhs_im)^2)

end
function sdp_3x3_to_soc_kim_kojima_conic(m, Mr, Mi)
    @assert size(Mr) == size(Mi)
    dim = size(Mr,1)

    cr = [1, 1]
    ci = [0, 0]
    for i in 1:dim
        dims = [delete!(Set(1:3), i)...]
        combs = [Combinatorics.combinations(dims,2)...]
        @show combs, i
        for comb in combs
            @show comb
            Ar = Mr[comb, comb]
            Ai = Mi[comb, comb]
            ar = Mr[comb, i]
            ai = Mi[comb, i]
            alphar = Mr[i, i]
            sdp_to_soc_kim_kojima_conic(m, Ar, Ai, ar, ai, alphar, cr, ci)
        end
    end
end

function sdp_3x3_to_soc_kim_kojima(m, Mr, Mi)
    @assert size(Mr) == size(Mi)
    dim = size(Mr,1)

    cr = [1, 1]
    ci = [0, 0]
    for i in 1:dim
        dims = [delete!(Set(1:3), i)...]
        combs = [Combinatorics.combinations(dims,2)...]
        @show combs, i
        for comb in combs
            @show comb
            Ar = Mr[comb, comb]
            Ai = Mi[comb, comb]
            ar = Mr[comb, i]
            ai = Mi[comb, i]
            alphar = Mr[i, i]
            sdp_to_soc_kim_kojima(m, Ar, Ai, ar, ai, alphar, cr, ci)
        end
    end
end
