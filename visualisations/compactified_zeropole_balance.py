# -*- coding: utf-8 -*-

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

# Function to map complex numbers onto the Riemann sphere
def riemann_sphere_projection(z):
    x = np.real(z) / (1 + abs(z)**2)
    y = np.imag(z) / (1 + abs(z)**2)
    z = (1 - abs(z)**2) / (1 + abs(z)**2)
    return x, y, z

# Generate points for the real axis (trivial zeros/poles)
real_line = np.linspace(-10, 10, 500) + 0j
x_real, y_real, z_real = riemann_sphere_projection(real_line)

# Generate points for the critical line (non-trivial zeros)
critical_line = 0.5 + 1j * np.linspace(-10, 10, 500)  # Full range to restore the entire circle
x_critical, y_critical, z_critical = riemann_sphere_projection(critical_line)

# Create the Riemann sphere plot
fig = plt.figure(figsize=(12, 10))
ax = fig.add_subplot(111, projection='3d')

# Plot the Riemann sphere
u = np.linspace(0, 2 * np.pi, 100)
v = np.linspace(0, np.pi, 100)
x_sphere = np.outer(np.cos(u), np.sin(v))
y_sphere = np.outer(np.sin(u), np.sin(v))
z_sphere = np.outer(np.ones(np.size(u)), np.cos(v))
ax.plot_surface(x_sphere, y_sphere, z_sphere, color='lightblue', alpha=0.3)

# Plot the real axis (trivial poles) - equatorial circle in the XY plane
x_eq = np.cos(u)
y_eq = np.sin(u)
z_eq = np.zeros_like(x_eq)
ax.plot(x_eq, y_eq, z_eq, color='red', linewidth=2, label='Normalized Real Axis')

# Plot the critical line (full vertical circle passing through poles)
x_vert = np.zeros_like(u)
y_vert = np.cos(u)
z_vert = np.sin(u)
ax.plot(x_vert, y_vert, z_vert, color='green', linewidth=2, label='Normalized Imaginary Axis')

    
# Add dashed lines mapping from the negative real axis to the upper part of the critical line
num_correspondences = 6  # Number of dashed lines to keep (leftmost ones)
selected_indices = [1, 2, 3]  # Select the leftmost indices for mapping
half_range = len(u) // 2  # Define half of the points for the upper half mappings


for i in selected_indices:
    idx = half_range // num_correspondences * i
#    idx = len(x_eq) // 8 * i  # Adjust for spacing to get leftmost connections
    ax.plot([x_eq[idx], x_vert[idx]], 
            [y_eq[idx], y_vert[idx]], 
            [z_eq[idx], z_vert[idx]], 
            linestyle='dashed', color='blue', alpha=0.7)


# Adjust the viewing angle to position axes correctly
ax.view_init(elev=20, azim=120)  # Rotate to place real axis front-left and imaginary back-right

# Add directional labels for normalized axes with correct placement
ax.text(1.05, 0, 0, "- (Re)", color='black', fontsize=12)  # Real axis left
ax.text(-1.05, 0, 0, "+ (Re)", color='black', fontsize=12)  # Real axis right
ax.text(0, 1.05, 0, "- (Im)", color='black', fontsize=12)   # Imaginary axis left
ax.text(0, -1.05, 0, "+ (Im)", color='black', fontsize=12)  # Imaginary axis right

# Highlight the south pole (origin) and north pole (infinity)
south_pole = np.array([0, 0, -1])  # South pole at (0, 0, -1)
north_pole = np.array([0, 0, 1])   # North pole at (0, 0, 1)

# Plot the south pole (origin)
ax.scatter(*south_pole, color='blue', s=100, label='Origin (0)')
ax.text(0, 0, -1.1, 'Origin (0)', color='blue', fontsize=12, ha='center')

# Plot the north pole (point at infinity)
ax.scatter(*north_pole, color='red', s=100, label='Infinity (∞)')
ax.text(0, 0, 1.1, 'Infinity (∞)', color='red', fontsize=12, ha='center')

# Remove axis numerical ticks for minimalistic style
ax.set_xticks([])
ax.set_yticks([])
ax.set_zticks([])

# Update axis labels to correct orientation
ax.set_xlabel("Normalized Real Axis")
ax.set_ylabel("Normalized Imaginary Axis")
ax.set_zlabel("Projection Height")

# Customize the plot
ax.set_title("Riemann Sphere: Zeropole Balance with Shadow Function", fontsize=14)
ax.legend()

# Adjusting aspect ratio for better visualization
ax.set_box_aspect([1, 1, 1])  # Equal aspect ratio for all axes

# Save the plot as a PNG file in a specific directory
output_path = "/Users/attilacsordas/Desktop/rh/Proof_RH_via_Zeropole_Balance/visualisations/plot1_final.png"  # Replace with your directory
plt.savefig(output_path, dpi=300)
print(f"Plot saved to {output_path}")

# Show the plot
plt.show()



%\section{Supplementary Material}
%\label{sec:supp}
%The code generating the plots for the numerical evaluation of the exponential stabiliser of the shadow function can be found in the Jupyter Notebook, \texttt{Supp\_Mat\_Num\_Eval\_of\_Shadow\_Function\_Exponential\_Stabiliser.ipynb} and it is available at \href{https://github.com/attila-ac/Proof_RH_via_Zeropole_Balance}{GitHub} (\url{https://github.com/attila-ac/Proof_RH_via_Zeropole_Balance}). 

