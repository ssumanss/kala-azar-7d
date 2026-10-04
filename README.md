# Kala-azar 7D: Double Latency, Spectral Damping & Formal Stability Proofs

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Format: JSON](https://img.shields.io/badge/Format-JSON-blue.svg)](data/)
[![Lean 4: v4.16.0](https://img.shields.io/badge/Lean_4-v4.16.0-green.svg)](proofs/)
[![Tests: Pytest](https://img.shields.io/badge/Tests-Passing-brightgreen.svg)](tests/)

Open-access replication codebase, formal interactive theorem proving scripts in Lean 4, and epidemiological datasets accompanying the research letter:

> **"Double Latency and Global Stability in Kala-azar Dynamics"**  
> *Raj Kumar Raj and Sandeep Suman*  
> University Department of Mathematics, Tilka Manjhi Bhagalpur University, Bhagalpur 812007, Bihar, India.  
> *Applied Mathematics Letters (Elsevier), Submitted (2026).*

---

## Repository Overview

This repository provides full end-to-end reproducibility for the double-latency (SEIR$_H$--SEI$_V$) visceral leishmaniasis transmission model, including:
1. **Calibrated Parameters**: Empirical North Bihar epidemiological parameters for host and sandfly compartments.
2. **Spectral Analysis**: Next-Generation Matrix derivation and square-root incubation survival law linking $\mathcal{R}_0$ to sandfly EIP survival probability $P_{\mathrm{surv}}$.
3. **Formal Verification in Lean 4**: Zero-axiom machine-checked proofs of Lyapunov derivative bounds and positive definiteness.
4. **Numerical Simulation**: 7D ODE integration, time-series convergence, phase-space trajectories, and threshold sweeps.
5. **Automated Testing**: 100% passing pytest regression suite verifying invariance and derivative non-positivity.

```
kala-azar-7d/
├── README.md                                    # Replication guide, mathematical summary & documentation
├── LICENSE                                      # MIT Open Source License
├── pyproject.toml                               # Python project definition & dependencies
├── .gitignore
├── data/                                        # Calibrated epidemiological parameters
│   └── paper1b_baseline_parameters.json         # North Bihar baseline parameter dictionary
├── figures/                                     # Publication-grade vector (PDF) and raster (PNG) figures
│   ├── paper1b_simulation.pdf                   # Two-panel simulation: time-series convergence & R0 damping
│   └── paper1b_simulation.png                   # High-resolution raster (300 DPI)
├── proofs/                                      # Formal interactive theorem proving in Lean 4
│   ├── KalaAzarModelDoubleLatency.lean          # Lean 4 formal proofs of Lyapunov identities & damping law
│   ├── lakefile.lean                            # Lake package configuration (Mathlib v4.16.0)
│   └── lean-toolchain                           # Lean toolchain pin (v4.16.0)
├── scripts/                                     # Standalone numerical simulation & analysis pipeline
│   └── paper1b_double_latency.py                # 7D ODE solver, Lyapunov Lie derivatives & figure generator
└── tests/                                       # Automated regression and reproducibility tests
    └── test_reproducibility.py                  # Pytest suite asserting parameter invariance & V_dot <= 0
```

---

## Mathematical Model Formulation

The 7-dimensional compartmental ODE system models transmission between human hosts ($S_H, E_H, I_H, R_H$) and phlebotomine sandfly vectors ($S_V, E_V, I_V$):

$$
\begin{aligned}
\dot{S}_H &= \Lambda_H - a b_H \frac{I_V}{N_H} S_H - d_H S_H + \gamma R_H, \\
\dot{E}_H &= a b_H \frac{I_V}{N_H} S_H - (\sigma_H + d_H) E_H, \\
\dot{I}_H &= \sigma_H E_H - (\delta_H + d_H + r_H) I_H, \\
\dot{R}_H &= r_H I_H - (d_H + \gamma) R_H, \\
\dot{S}_V &= \Lambda_V - a b_V \frac{I_H}{N_H} S_V - d_V S_V, \\
\dot{E}_V &= a b_V \frac{I_H}{N_H} S_V - (\sigma_V + d_V) E_V, \\
\dot{I}_V &= \sigma_V E_V - d_V I_V.
\end{aligned}
$$

The biologically feasible compact invariant region is:

$$
\Omega_{7D} = \left\lbrace (S_H, E_H, I_H, R_H, S_V, E_V, I_V) \in \mathbb{R}_{\ge 0}^7 : N_H \le N_H^\ast = \frac{\Lambda_H}{d_H},\; N_V \le S_V^\ast = \frac{\Lambda_V}{d_V} \right\rbrace.
$$

---

## Core Theoretical Results

### 1. Square-Root Incubation Survival Law (Proposition 1)

Using the $4 \times 4$ Next-Generation Matrix (NGM) operator $\mathcal{F} \mathcal{V}^{-1}$, the basic reproduction number factors as:

$$
\mathcal{R}_{0} = \mathcal{R}_{0}^{\text{ideal}} \sqrt{\frac{\sigma_V}{\sigma_V + d_V}} = \mathcal{R}_{0}^{\text{ideal}} \sqrt{P_{\text{surv}}},
$$

where the benchmark under instantaneous vector incubation ($\sigma_V \to \infty$) is:

$$
\mathcal{R}_{0}^{\text{ideal}} = a \sqrt{\frac{b_H b_V \Lambda_V \sigma_H}{N_H^\ast d_V^2 (\sigma_H + d_H) k_H}},
$$

and $P_{\text{surv}} = \frac{\sigma_V}{\sigma_V + d_V}$ represents the probability that an infected sandfly survives the extrinsic incubation period (EIP).

For North Bihar baseline parameters ($\sigma_V = 1/7\ \text{d}^{-1}$, $d_V = 0.07\ \text{d}^{-1}$):

$$
\sqrt{P_{\text{surv}}} = \sqrt{\frac{0.1429}{0.1429 + 0.07}} \approx 0.8192 \implies 18.08\% \text{ reduction in } \mathcal{R}_0 \text{ relative to } \mathcal{R}_{0}^{\text{ideal}}.
$$

### 2. Global Asymptotic Stability of DFE (Theorem 1)

Consider the 4-term linear Lyapunov function with state-dependent weights:

$$
V(\mathbf{x}) = E_H + \frac{\sigma_H + d_H}{\sigma_H} I_H + c_3 E_V + \frac{a b_H}{d_V} I_V,
$$

where:

$$
c_3 = \frac{(\sigma_H + d_H) k_H N_H^\ast}{\sigma_H a b_V S_V^\ast}, \qquad k_H = \delta_H + d_H + r_H.
$$

The exact Lie derivative on $\Omega_{7D}$ satisfies:

$$
\dot{V}(\mathbf{x}) = a b_H \left( \frac{S_H}{N_H^\ast} - 1 \right) I_V + \frac{(\sigma_H + d_H) k_H}{\sigma_H} \left( \frac{S_V}{S_V^\ast} - 1 \right) I_H + c_3 (\sigma_V + d_V) (\mathcal{R}_{0,7D}^2 - 1) E_V \le 0.
$$

At the critical boundary $\mathcal{R}_{0,7D} = 1$, any candidate invariant orbit with $I_H > 0$ requires $S_V \equiv S_V^\ast \implies \dot{S}_V \equiv 0$, but evaluating the vector field yields:

$$
\dot{S}_V = -a b_V \frac{I_H}{N_H^\ast} S_V^\ast < 0,
$$

a strict contradiction. Hence, by LaSalle's Invariance Principle, the disease-free equilibrium $E_0$ is globally asymptotically stable on $\Omega_{7D}$ for all $\mathcal{R}_{0,7D} \le 1$.

---

## Baseline Parameter Calibrations (`data/paper1b_baseline_parameters.json`)

| Parameter | Description | Baseline Value | Biological Source |
|---|---|---|---|
| $\Lambda_H$ | Human daily recruitment | $0.55\ \text{day}^{-1}$ | Balances $d_H N_H^\ast$ ($N_H^\ast = 10^4$) |
| $d_H$ | Natural human mortality | $5.5 \times 10^{-5}\ \text{day}^{-1}$ | $\approx 50$-year lifespan |
| $\delta_H$ | VL-induced human mortality | $1.0 \times 10^{-3}\ \text{day}^{-1}$ | Untreated visceral leishmaniasis |
| $r_H$ | Human clinical recovery | $0.02\ \text{day}^{-1}$ | $\approx 50$-day treatment course |
| $\gamma$ | Human immunity waning | $2.7 \times 10^{-4}\ \text{day}^{-1}$ | $\approx 10$-year post-cure immunity |
| $\sigma_H$ | Human latency incubation rate | $1/90\ \text{day}^{-1}$ | $90$-day clinical latency (Stauch et al., 2011) |
| $\Lambda_V$ | Vector recruitment rate | $3500.0\ \text{day}^{-1}$ | Yields 5:1 vector-to-host density |
| $d_V$ | Adult sandfly mortality | $0.07\ \text{day}^{-1}$ | $\approx 14.3$-day life expectancy (Picado et al., 2010) |
| $a$ | Vector biting frequency | $0.25\ \text{day}^{-1}$ | 1 bite every 4 days |
| $b_H$ | Vector-to-host transmission prob | $0.15$ | Ready (2014) |
| $b_V$ | Host-to-vector transmission prob | $0.20$ | Ready (2014) |
| $\sigma_V$ | Vector extrinsic incubation rate | $1/7\ \text{day}^{-1}$ | 7-day EIP period (Ready, 2014) |

---

## Quickstart & Replication

### 1. Python Environment Setup
Using `uv` (recommended):
```bash
# Clone the repository
git clone https://github.com/ssumanss/kala-azar-7d.git
cd kala-azar-7d

# Run numerical simulation and regenerate figures
uv run python scripts/paper1b_double_latency.py

# Run the automated test suite
uv run pytest tests/ -v
```

### 2. Formal Proof Verification in Lean 4
To verify the machine-checked mathematical proofs:
```bash
cd proofs
lake build KalaAzarModelDoubleLatency
```
Verification confirms:
- `toProd7_injective`: Injectivity of the 7D state tuple mapping.
- `R0_7D_square_root_damping`: Proposition 1 scaling law.
- `V_7D_nonneg`: Non-negativity of $V(\mathbf{x}) \ge 0$ on $\Omega_{7D}$.
- `V_7D_dfe_zero`: $V(E_0) = 0$.
- `V_7D_infected_eq_zero_iff`: Positive definiteness ($V = 0 \iff E_H = I_H = E_V = I_V = 0$).
- `V_7D_dot_inequality`: Exact algebraic Lie derivative upper bound.
- `V_7D_dot_nonpos`: Proof of $\dot{V} \le 0$ when $\mathcal{R}_{0,7D} \le 1$.
- **0 errors, 0 warnings, 0 sorries, 0 custom axioms**.

---

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Citation

```bibtex
@article{raj2026doublelatency,
  title   = {Double Latency and Global Stability in Kala-azar Dynamics},
  author  = {Raj, Raj Kumar and Suman, Sandeep},
  journal = {Applied Mathematics Letters},
  year    = {2026},
  note    = {Submitted}
}
```
