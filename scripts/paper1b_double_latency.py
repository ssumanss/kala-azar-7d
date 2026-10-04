"""
paper1b_double_latency.py
=========================
Simulation, spectral analysis, parameter serialization, and Lyapunov verification for the
7-dimensional SEI_H R - SEI_V Kala-azar model.
Dedicated Open Science Replication Package for:
"Double Latency and Topological Stability in Kala-azar Dynamics" (Applied Mathematics Letters).
"""

from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")  # Force headless non-interactive backend
import matplotlib.pyplot as plt
from scipy.integrate import solve_ivp

REPO_ROOT = Path(__file__).resolve().parents[1]
DATA_DIR = REPO_ROOT / "data"
FIGURES_DIR = REPO_ROOT / "figures"

# Master baseline parameter dictionary for North Bihar calibrated 7D model
BASE_PARAMS_7D: dict = {
    "Lambda_H": 10000.0 * 5.5e-5,  # 0.55 day^-1 (balances d_H * N_H*)
    "d_H": 5.5e-5,                 # ~50-year human life expectancy
    "delta_H": 1.0e-3,              # untreated visceral leishmaniasis mortality
    "r_H": 0.02,                   # treatment recovery (~50-day duration)
    "gamma": 2.7e-4,               # waning immunity rate (~10 years)
    "sigma_H": 1.0 / 90.0,         # 90-day human incubation latency
    "Lambda_V": 3500.0,            # daily vector recruitment rate
    "d_V": 0.07,                   # adult sandfly natural mortality (~14-day lifespan)
    "a": 0.25,                     # biting frequency (1 bite every 4 days)
    "b_H": 0.15,                   # vector-to-host transmission probability
    "b_V": 0.20,                   # host-to-vector transmission probability
    "sigma_V": 1.0 / 7.0,          # 7-day vector extrinsic incubation period (EIP)
}


def serialize_table1_parameters() -> Path:
    """Serialize calibrated baseline parameters to JSON for Table 1 and data reproducibility."""
    out_file = DATA_DIR / "paper1b_baseline_parameters.json"
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    with open(out_file, "w", encoding="utf-8") as f:
        json.dump(BASE_PARAMS_7D, f, indent=2)
    return out_file


def compute_R0_ideal(p: dict) -> float:
    """
    Compute theoretical upper limit R0 under instantaneous vector incubation (sigma_V -> inf)
    via Next-Generation Matrix spectral radius.
    
    NGM Derivation Note:
    - Host force of infection transmits to E_H: F_13 = a * b_H.
    - Vector force of infection transmits to I_V: F_32 = a * b_V * (S_V^* / N_H^*).
    - At DFE, S_V^* = Lambda_V / d_V.
    - Vector transfer matrix exit rate is d_V, giving V_33^-1 = 1 / d_V.
    - The product F_13 * V_33^-1 * F_32 * V_21^-1 contains:
        (1 / d_V) [from V_33^-1] * (Lambda_V / d_V) [from S_V^*] = Lambda_V / d_V^2.
    - Hence d_V^2 emerges strictly from the combined vector demographic carrying capacity
      and adult vector infectious lifetime.
    """
    n_h_star = p["Lambda_H"] / p["d_H"]
    k_h = p["delta_H"] + p["d_H"] + p["r_H"]
    num = p["b_H"] * p["b_V"] * p["Lambda_V"] * p["sigma_H"]
    den = (p["d_V"] ** 2) * n_h_star * (p["sigma_H"] + p["d_H"]) * k_h
    return float(p["a"] * np.sqrt(num / den))


def compute_damping_factor(sigma_v: float, d_v: float) -> float:
    """Compute square-root vector latency damping factor sqrt(sigma_V / (sigma_V + d_V))."""
    return float(np.sqrt(sigma_v / (sigma_v + d_v)))


def compute_R0_7D(p: dict) -> float:
    """Compute R0 for 7D double-latency model."""
    r0_ideal = compute_R0_ideal(p)
    damping = compute_damping_factor(p["sigma_V"], p["d_V"])
    return float(r0_ideal * damping)


def double_latency_ode(t: float, y: list, p: dict) -> list:
    """Coupled 7D ODE system for SEIR_H - SEI_V transmission dynamics."""
    s_h, e_h, i_h, r_h, s_v, e_v, i_v = y
    n_h = s_h + e_h + i_h + r_h

    lambda_h = p["a"] * p["b_H"] * (i_v / n_h)
    lambda_v = p["a"] * p["b_V"] * (i_h / n_h)

    ds_h = p["Lambda_H"] - lambda_h * s_h - p["d_H"] * s_h + p["gamma"] * r_h
    de_h = lambda_h * s_h - (p["sigma_H"] + p["d_H"]) * e_h
    di_h = p["sigma_H"] * e_h - (p["delta_H"] + p["d_H"] + p["r_H"]) * i_h
    dr_h = p["r_H"] * i_h - (p["d_H"] + p["gamma"]) * r_h

    ds_v = p["Lambda_V"] - lambda_v * s_v - p["d_V"] * s_v
    de_v = lambda_v * s_v - (p["sigma_V"] + p["d_V"]) * e_v
    di_v = p["sigma_V"] * e_v - p["d_V"] * i_v

    return [ds_h, de_h, di_h, dr_h, ds_v, de_v, di_v]


def lyapunov_exact_derivative(y: list, p: dict) -> float:
    """
    Exact Lie derivative V_dot = grad(V) . f(x) evaluated along the autonomous
    constant-population (N_H = N_H*) vector field from manuscript Theorem 1:
    V(x) = c1*E_H + c2*I_H + c3*E_V + c4*I_V
    V_dot_exact = c1*dE_H/dt + c2*dI_H/dt + c3*dE_V/dt + c4*dI_V/dt
    """
    s_h, e_h, i_h, r_h, s_v, e_v, i_v = y

    n_h_star = p["Lambda_H"] / p["d_H"]
    s_v_star = p["Lambda_V"] / p["d_V"]
    k_h = p["delta_H"] + p["d_H"] + p["r_H"]

    # Autonomous constant-population vector field derivatives (Theorem 1 / LaSalle)
    de_h = p["a"] * p["b_H"] * (i_v / n_h_star) * s_h - (p["sigma_H"] + p["d_H"]) * e_h
    di_h = p["sigma_H"] * e_h - k_h * i_h
    de_v = p["a"] * p["b_V"] * (i_h / n_h_star) * s_v - (p["sigma_V"] + p["d_V"]) * e_v
    di_v = p["sigma_V"] * e_v - p["d_V"] * i_v

    # 4-term Lyapunov function weights: V(x) = c1*E_H + c2*I_H + c3*E_V + c4*I_V
    c1 = 1.0  # Normalized weight for E_H (c1 = 1 implicit in manuscript Theorem 1)
    c2 = (p["sigma_H"] + p["d_H"]) / p["sigma_H"]
    c3 = ((p["sigma_H"] + p["d_H"]) * k_h * n_h_star) / (
        p["sigma_H"] * p["a"] * p["b_V"] * s_v_star
    )
    c4 = p["a"] * p["b_H"] / p["d_V"]

    return float(c1 * de_h + c2 * di_h + c3 * de_v + c4 * di_v)


def lyapunov_derivative_upper_bound(y: list, p: dict) -> float:
    """
    Algebraic upper bound on V_dot in Omega_7D used for LaSalle invariance analysis:
    V_dot <= a*b_H*I_V*(S_H/N_H* - 1)
           + ((sigma_H+d_H)*k_H/sigma_H)*I_H*(S_V/S_V* - 1)
           + c3*(sigma_V+d_V)*(R0_7D^2 - 1)*E_V
    """
    s_h, e_h, i_h, r_h, s_v, e_v, i_v = y
    n_h_star = p["Lambda_H"] / p["d_H"]
    s_v_star = p["Lambda_V"] / p["d_V"]
    k_h = p["delta_H"] + p["d_H"] + p["r_H"]

    # 4-term Lyapunov weights: c1 = 1.0, c2 = (sigma_H+d_H)/sigma_H, c3, c4 = a*b_H/d_V
    c1 = 1.0  # Normalized weight for E_H (implicit)
    c2 = (p["sigma_H"] + p["d_H"]) / p["sigma_H"]
    c3 = ((p["sigma_H"] + p["d_H"]) * k_h * n_h_star) / (
        p["sigma_H"] * p["a"] * p["b_V"] * s_v_star
    )
    c4 = p["a"] * p["b_H"] / p["d_V"]
    r0_7d = compute_R0_7D(p)

    term1 = c4 * p["d_V"] * i_v * (s_h / n_h_star - 1.0)  # c4*d_V = a*b_H
    term2 = c2 * k_h * i_h * (s_v / s_v_star - 1.0)
    term3 = c3 * (p["sigma_V"] + p["d_V"]) * (r0_7d**2 - 1.0) * e_v

    return float(term1 + term2 + term3)


def run_paper1b_simulation() -> None:
    """Run numerical integration, serialize parameters, and plot the 2-panel publication figure."""
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)

    # Serialize baseline parameters for Table 1 reproducibility
    serialize_table1_parameters()

    t_span = (0.0, 1500.0)
    t_eval = np.linspace(0.0, 1500.0, 3000)

    n_h_star = BASE_PARAMS_7D["Lambda_H"] / BASE_PARAMS_7D["d_H"]
    s_v_star = BASE_PARAMS_7D["Lambda_V"] / BASE_PARAMS_7D["d_V"]

    # Initial condition: small introduction of infected hosts and vectors
    y0 = [n_h_star - 10.0, 5.0, 5.0, 0.0, s_v_star - 50.0, 30.0, 20.0]

    # Subcritical scenario: biting rate reduced to a=0.08
    sub_params = dict(BASE_PARAMS_7D)
    sub_params["a"] = 0.08
    r0_sub = compute_R0_7D(sub_params)
    sol_sub = solve_ivp(
        double_latency_ode, t_span, y0, args=(sub_params,), t_eval=t_eval, rtol=1e-8, atol=1e-10
    )

    # Supercritical scenario: baseline biting rate a=0.25
    r0_sup = compute_R0_7D(BASE_PARAMS_7D)
    sol_sup = solve_ivp(
        double_latency_ode, t_span, y0, args=(BASE_PARAMS_7D,), t_eval=t_eval, rtol=1e-8, atol=1e-10
    )

    # Sweep transmission biting rate 'a' for R0 comparison
    a_vals = np.linspace(0.05, 0.35, 200)

    # Matplotlib styling for academic publication
    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["Times New Roman", "DejaVu Serif", "Computer Modern Roman"],
        "mathtext.fontset": "cm",
        "font.size": 10,
        "axes.labelsize": 10.0,
        "axes.titlesize": 10.5,
        "legend.fontsize": 7.5,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "figure.autolayout": True,
    })

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.8, 3.3), dpi=300)

    # Panel (a): Time series trajectories with dynamic R0 formatted strings
    ax1.plot(
        sol_sub.t,
        sol_sub.y[2],
        color="#1b4f72",
        linestyle="--",
        linewidth=1.8,
        label="Subcritical",
    )
    ax1.plot(
        sol_sup.t,
        sol_sup.y[2],
        color="#900c3f",
        linestyle="-",
        linewidth=2.0,
        label="Supercritical",
    )

    # Peak annotation on supercritical curve (positioned in wide open canyon between summit and inset)
    peak_idx = int(np.argmax(sol_sup.y[2]))
    peak_t = float(sol_sup.t[peak_idx])
    peak_val = float(sol_sup.y[2][peak_idx])
    ax1.plot(peak_t, peak_val, marker="o", markersize=4.5, color="#900c3f", zorder=5)
    ax1.annotate(
        rf"Peak: {peak_val:.0f} cases" "\n" rf"($t = {peak_t:.0f}\ \text{{d}},\ \mathcal{{R}}_0 = {r0_sup:.2f}$)",
        xy=(peak_t, peak_val),
        xytext=(peak_t + 85, peak_val + 130),
        fontsize=7.2,
        ha="center",
        va="center",
        color="#900c3f",
        fontweight="bold",
        arrowprops=dict(arrowstyle="->", color="#900c3f", lw=0.9),
        bbox=dict(boxstyle="round,pad=0.2", facecolor="white", edgecolor="#900c3f", alpha=0.95, lw=0.6),
        zorder=6,
    )

    ax1.set_xlabel("Time (days)")
    ax1.set_ylabel(r"Infectious Hosts $I_H(t)$")
    ax1.set_title("(a) Asymptotic Stability & Persistence")
    ax1.grid(True, linestyle=":", alpha=0.5)
    ax1.set_xlim(-20, 1520)
    ax1.set_ylim(-40, 1680)
    ax1.legend(
        loc="upper left",
        bbox_to_anchor=(0.02, 0.98),
        frameon=True,
        framealpha=0.95,
        edgecolor="#d5d8dc",
        fontsize=7.0,
        handlelength=1.0,
        handletextpad=0.3,
        borderpad=0.25,
    )

    # Inset for subcritical clearance to E_0 (positioned cleanly in upper-right quadrant)
    ax_ins = ax1.inset_axes([0.62, 0.46, 0.35, 0.48])
    ax_ins.set_facecolor("#fafbfc")
    mask = sol_sub.t <= 500
    ax_ins.plot(sol_sub.t[mask], sol_sub.y[2][mask], color="#1b4f72", linestyle="--", linewidth=1.8)
    ax_ins.plot(0, sol_sub.y[2][0], marker="o", markersize=3.5, color="#1b4f72")
    ax_ins.text(
        0.95,
        0.88,
        r"Subcritical ($E_0$)" "\n" rf"$\mathcal{{R}}_0 = {r0_sub:.2f}$",
        transform=ax_ins.transAxes,
        ha="right",
        va="top",
        fontsize=7.0,
        fontweight="bold",
        color="#1b4f72",
    )
    ax_ins.set_xlabel("Time (days)", fontsize=7, labelpad=2)
    ax_ins.set_ylabel(r"$I_H(t)$", fontsize=7, labelpad=2)
    ax_ins.tick_params(labelsize=6.5, pad=1.5)
    ax_ins.grid(True, linestyle=":", alpha=0.45)
    ax_ins.set_xlim(0, 500)
    ax_ins.set_ylim(0, 5.5)

    # Panel (b): 7D reproduction number R0 across biting frequency for varying sandfly EIP
    eip_scenarios = [
        {"days": 4.0, "sigma_V": 1.0 / 4.0, "color": "#2980b9", "ls": "--", "label": r"Rapid EIP ($1/\sigma_V = 4$ d)"},
        {"days": 7.0, "sigma_V": 1.0 / 7.0, "color": "#1e8449", "ls": "-", "label": r"Baseline EIP ($1/\sigma_V = 7$ d)"},
        {"days": 12.0, "sigma_V": 1.0 / 12.0, "color": "#d35400", "ls": "-.", "label": r"Prolonged EIP ($1/\sigma_V = 12$ d)"},
    ]

    for sc in eip_scenarios:
        r0_curve = []
        for a_val in a_vals:
            p_temp = dict(BASE_PARAMS_7D)
            p_temp["a"] = a_val
            p_temp["sigma_V"] = sc["sigma_V"]
            r0_curve.append(compute_R0_7D(p_temp))

        ax2.plot(
            a_vals,
            r0_curve,
            color=sc["color"],
            linestyle=sc["ls"],
            linewidth=1.8,
            label=sc["label"],
        )

        # Critical biting threshold a* where R0 = 1
        sqrt_val = compute_R0_7D({**BASE_PARAMS_7D, "sigma_V": sc["sigma_V"]}) / BASE_PARAMS_7D["a"]
        a_crit = 1.0 / sqrt_val
        ax2.plot(a_crit, 1.0, marker="|", color=sc["color"], markersize=7, mew=1.5)

    ax2.axhline(1.0, color="#2c3e50", linestyle="--", linewidth=0.9, alpha=0.8, label=r"Threshold $\mathcal{R}_0 = 1$")

    # Baseline operating point at a=0.25 on the 7-day EIP curve
    a_base = BASE_PARAMS_7D["a"]
    r0_base = compute_R0_7D(BASE_PARAMS_7D)
    ax2.plot(a_base, r0_base, marker="o", markersize=4.5, color="#1e8449", zorder=5)
    ax2.annotate(
        rf"Baseline: $\mathcal{{R}}_0 = {r0_base:.2f}$" "\n" rf"($a = {a_base:.2f}\ \text{{d}}^{{-1}}$)",
        xy=(a_base, r0_base),
        xytext=(a_base - 0.055, r0_base + 0.35),
        fontsize=7.6,
        fontweight="bold",
        ha="center",
        va="center",
        color="#1e8449",
        arrowprops=dict(arrowstyle="->", color="#1e8449", lw=0.9),
        bbox=dict(boxstyle="round,pad=0.25", facecolor="white", edgecolor="#1e8449", lw=0.7, alpha=0.96),
        zorder=6,
    )

    # Annotate critical threshold for baseline EIP = 7 days
    sqrt_base = r0_base / a_base
    a_crit_base = 1.0 / sqrt_base
    ax2.annotate(
        rf"Critical $a^* = {a_crit_base:.3f}\ \text{{d}}^{{-1}}$",
        xy=(a_crit_base, 1.0),
        xytext=(a_crit_base + 0.035, 0.55),
        fontsize=7.4,
        ha="left",
        va="center",
        color="#1e8449",
        arrowprops=dict(arrowstyle="->", color="#1e8449", lw=0.9),
        bbox=dict(boxstyle="round,pad=0.2", facecolor="white", edgecolor="none", alpha=0.88),
    )

    ax2.set_xlabel(r"Vector Biting Rate $a$ ($\text{day}^{-1}$)")
    ax2.set_ylabel(r"Basic Reproduction Number $\mathcal{R}_0$")
    ax2.set_title(r"(b) Transmission Thresholds vs. EIP Latency")
    ax2.set_xlim(0.05, 0.35)
    ax2.set_ylim(0.2, 3.6)
    ax2.grid(True, linestyle=":", alpha=0.5)
    ax2.legend(
        loc="upper left",
        frameon=True,
        framealpha=0.95,
        edgecolor="#d5d8dc",
        fontsize=7.2,
        handlelength=1.4,
        handletextpad=0.4,
        borderpad=0.35,
    )

    fig.savefig(FIGURES_DIR / "paper1b_simulation.pdf", format="pdf", bbox_inches="tight")
    fig.savefig(FIGURES_DIR / "paper1b_simulation.png", format="png", dpi=300, bbox_inches="tight")

    plt.close(fig)
    print(f"Success! Written figures to: {FIGURES_DIR / 'paper1b_simulation.pdf'}")


if __name__ == "__main__":
    run_paper1b_simulation()
