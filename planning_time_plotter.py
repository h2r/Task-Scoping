from matplotlib import pyplot as plt
import numpy as np


def errorfill(x, y, yerr, color=None, alpha_fill=0.3, ax=None, linestyle=None, plt_label=None, marker=None, alpha=None, linewidth=None):
    ax = ax if ax is not None else plt.gca()
    # if color is None:
    #     color = ax._get_lines.color_cycle.next()
    if np.isscalar(yerr) or len(yerr) == len(y):
        ymin = y - yerr
        ymax = y + yerr
    elif len(yerr) == 2:
        ymin, ymax = yerr
    #ax.errorbar(x, y, yerr=yerr, ecolor=color, label=plt_label)
    ax.plot(x, y, color=color, label=plt_label, linestyle=linestyle, marker=marker, alpha=alpha, linewidth=linewidth)
    #ax.errorbar(x, y, yerr = ymax - y, label=plt_label, linestyle=linestyle, color=color)
    ax.fill_between(x, ymax, ymin, color=color, alpha=alpha_fill)

def plot():
    plt.figure(1)

    domain_num = np.log10(np.array([5.37*(10 ** 16),8.59*(10 ** 16),1.37 * (10 ** 19),2.20 * (10 ** 20),3.52 * (10 ** 21)]))

    planner_time = np.array([10.4528, 17.9689, 23.0667, 28.284, 29.4582])
    planner_stddev = np.array([0.3371968762,0.4784970568,0.8237816661,0.3609755301,0.6369407438])
    planner_with_error = [planner_time - planner_stddev, planner_time + planner_stddev]

    planner_and_scoper_time = np.array([10.8319,11.3166,11.7695,13.016,13.9471])
    planner_and_scoper_stddev = np.array([0.4240753209,0.3971817944,0.5309587241,0.4835011203,0.2006885093])
    pands_with_error = [planner_and_scoper_time - planner_and_scoper_stddev, planner_and_scoper_time + planner_and_scoper_stddev]

    errorfill(domain_num, planner_time, yerr=planner_with_error, color='red', linestyle='-', plt_label='ENHSP-2020', marker='o')
    errorfill(domain_num, planner_and_scoper_time, yerr=pands_with_error, color='blue', linestyle='-', plt_label='TS (ours) + ENHSP-2020', marker = 'o')

    plt.xlabel('Log size of domain (base 10)')
    plt.ylabel('Wall clock time taken to find plan/s')
    plt.title('Planning time vs. log. domain size')
#    plt.legend(bbox_to_anchor=(1.05, 1), loc='upper left', borderaxespad=0.)
    plt.legend()

    plt.show()

if __name__ == '__main__':
    plot()