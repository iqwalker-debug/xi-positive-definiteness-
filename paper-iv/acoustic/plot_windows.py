"""Plot the training-equalized ACE results from window-results.json."""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import FormatStrFormatter

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "manuscript" / "acoustic-windows.png"


def draw():
    data = json.loads((HERE / "window-results.json").read_text())
    rows = data["windows"]
    scores = [row["weightings"]["equalized"] for row in rows]
    y = np.arange(len(rows))
    labels = [f'{r["start"]}–{r["end"]}' + ("*" if r["role"] == "reported" else "")
              for r in rows]

    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 8.5,
                         "axes.labelcolor": "#20323d", "text.color": "#20323d",
                         "xtick.color": "#32444f", "ytick.color": "#32444f"})
    fig, (left, right) = plt.subplots(1, 2, figsize=(6.9, 3.4), sharey=True)
    fig.subplots_adjust(left=.126, right=.97, bottom=.25, top=.83, wspace=.2)
    teal, orange, grey = "#11645c", "#a64a19", "#606a73"
    for panel in (left, right):
        panel.axhspan(4.53, 5.47, color="#f9e8de", lw=0, zorder=0)
        panel.set_axisbelow(True)
        panel.grid(axis="x", color="#e1e6e9", lw=.7)
        panel.spines[["left", "top", "right"]].set_visible(False)
        panel.spines["bottom"].set_color("#aebcc2")
        panel.tick_params(axis="y", length=0)
        panel.tick_params(axis="x", width=.5, length=3)
        panel.xaxis.set_major_formatter(FormatStrFormatter("%.2f"))
    left.set_ylim(len(rows)-.5, -.5)
    left.set_yticks(y, labels)
    left.set_ylabel("Interval (s)")
    left.set_title("A   Signed odd correlation", loc="left", fontsize=10.4, fontweight="bold", pad=8)
    right.set_title("B   Prediction error", loc="left", fontsize=10.4, fontweight="bold", pad=8)
    left.axvline(0, color="#77858e", lw=1)
    averages = np.array([[np.mean(s["odd_pairs"][:7]), np.mean(s["odd_pairs"][7:])]
                         for s in scores])
    left.hlines(y, averages[:, 0], averages[:, 1], color="#a5b9b9", lw=1.5)
    left.scatter(averages[:, 0], y, color=teal, s=23, label="6 cm", zorder=3)
    left.scatter(averages[:, 1], y, color=orange, s=21, marker="D", label="12 cm", zorder=3)
    left.set(xlim=(-.145,.25), xticks=[-.1, 0, .1, .2], xlabel="Mean across pairs at each spacing")
    for key, label, mark, color, shift in [("zero", "Zero", "o", grey, -.12),
                                           ("forward", "Forward", "s", teal, 0),
                                           ("reversed", "Reversed", "^", orange, .12)]:
        right.scatter([s["mae"][key] for s in scores], y+shift, c=color,
                      marker=mark, s=23, label=label, zorder=3)
    right.set(xlim=(-.01, .253), xticks=[0,.05,.10,.15,.20,.25], xlabel="Mean absolute error across 13 pairs")
    for panel, cols in ((left, 2), (right, 3)):
        panel.legend(loc="upper center", bbox_to_anchor=(.5, 1.32), ncol=cols, fontsize=8,
                     handlelength=.9, handletextpad=.35, columnspacing=.9, frameon=False)
    fig.text(.126, .044, "* Previously reported window. Other windows were examined post hoc. Training-equalized band, 200–1,600 Hz.",
             fontsize=7.4)
    fig.savefig(OUT, dpi=220, facecolor="white")
    plt.close(fig)


if __name__ == "__main__":
    draw()
