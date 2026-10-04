"""
test_reproducibility.py
=======================
Automated reproducibility and mathematical invariance tests for:
"Double Latency and Topological Stability in Kala-azar Dynamics" (Applied Mathematics Letters).
"""

from pathlib import Path
import json
import sys
import numpy as np
import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS_DIR = str(REPO_ROOT / "scripts")
if SCRIPTS_DIR not in sys.path:
    sys.path.insert(0, SCRIPTS_DIR)

from paper1b_double_latency import (
    BASE_PARAMS_7D,
    compute_R0_ideal,
    compute_R0_7D,
    compute_damping_factor,
    double_latency_ode,
    run_paper1b_simulation,
    serialize_table1_parameters,
    lyapunov_exact_derivative,
    lyapunov_derivative_upper_bound,
)


def test_baseline_parameters_serialization() -> None:
    """Verify that serialize_table1_parameters() produces a valid JSON file matching BASE_PARAMS_7D."""
    out_file = serialize_table1_parameters()
    assert out_file.exists(), f"Missing parameter file {out_file}"
    with open(out_file, "r", encoding="utf-8") as f:
        loaded = json.load(f)
    assert loaded["Lambda_V"] == 3500.0
    assert np.isclose(loaded["d_V"], 0.07)
    assert np.isclose(loaded["sigma_H"], 1.0 / 90.0)
    assert np.isclose(loaded["sigma_V"], 1.0 / 7.0)


def test_square_root_scaling_law_baseline() -> None:
    """Verify that R0_7D = R0_ideal * sqrt(sigma_V / (sigma_V + d_V)) at baseline."""
    r0_ideal = compute_R0_ideal(BASE_PARAMS_7D)
    r0_7d = compute_R0_7D(BASE_PARAMS_7D)
    damping = compute_damping_factor(BASE_PARAMS_7D["sigma_V"], BASE_PARAMS_7D["d_V"])
    
    assert np.isclose(r0_7d, r0_ideal * damping, atol=1e-12)
    # Baseline with Lambda_V=3500, d_V=0.07 yields 18.08% reduction
    reduction = 1.0 - damping
    assert np.isclose(reduction, 0.180768, atol=1e-4)


def test_scaling_law_invariance_across_random_draws() -> None:
    """Verify the square-root damping identity across 1,000 random parameter draws."""
    rng = np.random.default_rng(seed=42)
    for _ in range(1000):
        params = {
            "Lambda_H": rng.uniform(0.1, 2.0),
            "d_H": rng.uniform(1e-5, 1e-4),
            "delta_H": rng.uniform(1e-4, 5e-3),
            "r_H": rng.uniform(0.005, 0.05),
            "gamma": rng.uniform(1e-4, 1e-3),
            "sigma_H": rng.uniform(1.0 / 180.0, 1.0 / 30.0),
            "Lambda_V": rng.uniform(1000.0, 10000.0),
            "d_V": rng.uniform(0.02, 0.15),
            "a": rng.uniform(0.1, 0.5),
            "b_H": rng.uniform(0.05, 0.4),
            "b_V": rng.uniform(0.05, 0.4),
            "sigma_V": rng.uniform(1.0 / 14.0, 1.0 / 3.0),
        }
        r0_id = compute_R0_ideal(params)
        r0_7 = compute_R0_7D(params)
        damping = compute_damping_factor(params["sigma_V"], params["d_V"])
        assert np.isclose(r0_7, r0_id * damping, rtol=1e-12, atol=1e-12)


def test_lyapunov_derivative_nonpositive_when_r0_subcritical() -> None:
    """Verify exact Lie derivative V_dot <= 0 and algebraic upper bound <= 0 for 1,000 points in Omega_7D when R0_7D <= 1."""
    rng = np.random.default_rng(seed=123)
    subcrit_params = dict(BASE_PARAMS_7D)
    subcrit_params["a"] = 0.08  # forces R0_7D < 1 (~0.66)
    r0_7d = compute_R0_7D(subcrit_params)
    assert r0_7d < 1.0

    n_h_star = subcrit_params["Lambda_H"] / subcrit_params["d_H"]
    s_v_star = subcrit_params["Lambda_V"] / subcrit_params["d_V"]

    for _ in range(1000):
        # Sample state inside biologically feasible compact domain Omega_7D
        h_shares = rng.dirichlet(np.ones(4))
        h_total = rng.uniform(0.1 * n_h_star, n_h_star)
        s_h, e_h, i_h, r_h = h_shares * h_total

        v_shares = rng.dirichlet(np.ones(3))
        v_total = rng.uniform(0.1 * s_v_star, s_v_star)
        s_v, e_v, i_v = v_shares * v_total

        y = [s_h, e_h, i_h, r_h, s_v, e_v, i_v]

        v_dot_exact = lyapunov_exact_derivative(y, subcrit_params)
        v_dot_bound = lyapunov_derivative_upper_bound(y, subcrit_params)

        assert v_dot_exact <= 1e-12, f"Exact Lie derivative positive: {v_dot_exact}"
        assert v_dot_bound <= 1e-12, f"LaSalle upper bound positive: {v_dot_bound}"
        assert np.isclose(v_dot_exact, v_dot_bound, atol=1e-11), (
            f"Exact ({v_dot_exact}) and upper bound ({v_dot_bound}) mismatch!"
        )


def test_simulation_outputs_generated() -> None:
    """Verify that running the simulation script populates parameter JSON and figures."""
    run_paper1b_simulation()
    assert (REPO_ROOT / "data" / "paper1b_baseline_parameters.json").exists()
    assert (REPO_ROOT / "figures" / "paper1b_simulation.pdf").exists()
    assert (REPO_ROOT / "figures" / "paper1b_simulation.png").exists()
