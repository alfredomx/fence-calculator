# Fence Estimator

Herramienta web para dibujar el croquis de una cerca residencial (estilo work-order
de subcontratistas de cercas) y calcular los materiales automáticamente.

- **App:** [`app/`](app/) — vanilla JS + SVG, sin build. Abrir `app/index.html` desde
  cualquier hosting estático, o localmente con `python app/serve.py` (puerto 8123,
  sin caché para desarrollo).
- Dibujo: tap para trazar, clic derecho en la línea agrega poste (split), estilos por
  sección (rails 2/3, Standard/GN/Cap&Trim, 1x4/1x6, MP/WP) con defaults de proyecto
  y overrides por pared.
- Materiales: postes, rieles, tablas, cap & trim, clavos (clips/rolls) y misc,
  calculados del dibujo con cantidades ajustables a mano.
