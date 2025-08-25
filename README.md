# VGA Car Project

## 🎯 Project Overview
This project uses a Nexys A7 Atrix 7 (designed in SystemVerilog with Vivado) to display a simple **2D car** on a **black VGA background**.  
The car’s position is controlled by the FPGA board’s **directional buttons** (up, down, left, right).  

The design demonstrates:
- VGA signal generation (horizontal & vertical sync counters).
- Pixel generation logic.
- A simple object rendering pipeline.
- Real-time user interaction through board I/O.