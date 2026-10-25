import { VGroup, parseSVGPathData } from './vendor/manim-web.js';
import { SVG } from './vendor/MathJaxBundle-DRYv6mR0.js';
import { ar as Mesh, qt as Group, ra as Shape, Or as Path, ia as ShapeGeometry, ta as ShaderMaterial, pa as SphereGeometry, j as BufferGeometry, A as BufferAttribute, Dt as DynamicDrawUsage } from './vendor/three.core-FQGwh_Lt.js';

const vertex = 'varying vec3 n; varying vec3 local; void main(){local=normalize(position);n=normalize(normalMatrix*normal);gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.0);}';
const surfaceFragment = 'varying vec3 n; void main(){float z=abs(normalize(n).z);float w=max(fwidth(z),.0001);float ink=1.0-smoothstep(.25*w,1.6*w,z);gl_FragColor=vec4(vec3(1.0-ink),1.0);}';
const ballFragment = [
  'varying vec3 n;',
  'varying vec3 local;',
  'void main(){',
  'vec3 normal=normalize(n), p=normalize(local);',
  'float light=max(0.0,dot(normal,normalize(vec3(-.5,.7,1.0))));',
  'float shine=pow(max(0.0,dot(normal,normalize(vec3(-.35,.5,1.0)))),28.0);',
  'vec3 color=vec3(.003+.013*light+.075*shine);',
  'float edge=fwidth(abs(p.z));',
  'float disk=smoothstep(.9075-edge,.9075+edge,abs(p.z));',
  'vec3 white=vec3(.94+.06*light);',
  'gl_FragColor=vec4(mix(color,white,disk),1.0);',
  '}'
].join('\n');

export function createGeometry(scene) {
  const anchor = new VGroup();
  const group = new Group(), left = new Group(), axis = new Group(), spin = new Group();
  const resources = [];
  const own = value => (resources.push(value), value);
  const rows = 80, columns = 128;
  const positions = new Float32Array((rows + 1) * (columns + 1) * 3);
  const normals = new Float32Array(positions.length);
  const indices = new Uint16Array(rows * columns * 6);
  let cursor = 0;
  for (let row = 0; row < rows; row++) for (let col = 0; col < columns; col++) {
    const a = row * (columns + 1) + col, b = a + columns + 1;
    indices.set([a, b, b + 1, a, b + 1, a + 1], cursor);
    cursor += 6;
  }
  const surfaceGeometry = own(new BufferGeometry());
  surfaceGeometry.setAttribute('position', new BufferAttribute(positions, 3).setUsage(DynamicDrawUsage));
  surfaceGeometry.setAttribute('normal', new BufferAttribute(normals, 3).setUsage(DynamicDrawUsage));
  surfaceGeometry.setIndex(new BufferAttribute(indices, 1));
  const surfaceMaterial = own(new ShaderMaterial({ vertexShader: vertex, fragmentShader: surfaceFragment, side: 2, depthWrite: true, polygonOffset: true, polygonOffsetFactor: 1, polygonOffsetUnits: 1 }));
  const surface = new Mesh(surfaceGeometry, surfaceMaterial);
  surface.frustumCulled = false;
  surface.renderOrder = 0;
  const outlineMaterial = own(new ShaderMaterial({
    vertexShader: 'void main(){vec4 p=modelViewMatrix*vec4(position,1.0);vec2 direction=(normalMatrix*normal).xy;p.xy+=.03*direction/max(length(direction),.000001);gl_Position=projectionMatrix*p;}',
    fragmentShader: 'void main(){gl_FragColor=vec4(0.0,0.0,0.0,1.0);}',
    side: 1, depthWrite: false, depthTest: false
  }));
  const outline = new Mesh(surfaceGeometry, outlineMaterial);
  outline.frustumCulled = false;
  outline.renderOrder = -1;
  left.add(outline, surface);

  const ringVertex = 'attribute float arc; varying float angle; void main(){angle=arc;gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.0);}';
  const solidMaterial = own(new ShaderMaterial({ vertexShader: ringVertex, fragmentShader: 'void main(){gl_FragColor=vec4(0.0,0.0,0.0,1.0);}', side: 2, depthWrite: false, depthFunc: 3 }));
  const hiddenMaterial = own(new ShaderMaterial({ vertexShader: ringVertex, fragmentShader: 'varying float angle; void main(){if(fract(angle*12.0/3.14159265359)>.58) discard;gl_FragColor=vec4(0.0,0.0,0.0,1.0);}', side: 2, depthWrite: false, depthFunc: 6 }));
  const rings = Array.from({ length: 3 }, () => {
    const sides = 8, points = new Float32Array((columns + 1) * (sides + 1) * 3);
    const arc = new Float32Array((columns + 1) * (sides + 1)), order = new Uint16Array(columns * sides * 6);
    let offset = 0;
    for (let col = 0; col <= columns; col++) for (let side = 0; side <= sides; side++) arc[col * (sides + 1) + side] = col * Math.PI * 2 / columns;
    for (let col = 0; col < columns; col++) for (let side = 0; side < sides; side++) {
      const a = col * (sides + 1) + side, b = a + sides + 1;
      order.set([a, b, a + 1, b, b + 1, a + 1], offset);
      offset += 6;
    }
    const geometry = own(new BufferGeometry());
    geometry.setAttribute('position', new BufferAttribute(points, 3).setUsage(DynamicDrawUsage));
    geometry.setAttribute('arc', new BufferAttribute(arc, 1));
    geometry.setIndex(new BufferAttribute(order, 1));
    const front = new Mesh(geometry, solidMaterial), back = new Mesh(geometry, hiddenMaterial);
    front.frustumCulled = back.frustumCulled = false;
    front.renderOrder = 2;
    back.renderOrder = 1;
    left.add(back, front);
    return { geometry, points, front, back, sides };
  });

  const ball = new Mesh(own(new SphereGeometry(1.78, 112, 80)), own(new ShaderMaterial({ vertexShader: vertex, fragmentShader: ballFragment })));
  const glyph = new SVG().font.getChar('normal', 0x38)[3].p;
  const paths = parseSVGPathData('M' + glyph).map((points, index) => {
    const path = index ? new Path() : new Shape();
    path.moveTo(...points[0]);
    for (let i = 1; i < points.length; i += 3) path.bezierCurveTo(...points[i], ...points[i + 1], ...points[i + 2]);
    path.closePath();
    return path;
  });
  paths[0].holes.push(...paths.slice(1));
  const shape = new ShapeGeometry(paths[0], 20), flat = shape.toNonIndexed(), triangles = [];
  const vertices = flat.attributes.position.array;
  function split(a, b, c, depth) {
    if (!depth) { triangles.push(...a, ...b, ...c); return; }
    const ab = a.map((value, i) => (value + b[i]) / 2), bc = b.map((value, i) => (value + c[i]) / 2), ca = c.map((value, i) => (value + a[i]) / 2);
    split(a, ab, ca, depth - 1);
    split(ab, b, bc, depth - 1);
    split(ca, bc, c, depth - 1);
    split(ab, bc, ca, depth - 1);
  }
  for (let i = 0; i < vertices.length; i += 9) {
    const points = [];
    for (let j = 0; j < 9; j += 3) points.push([(vertices[i + j] - 250) * .95 / 688, (vertices[i + j + 1] - 322) * .95 / 688, 0]);
    split(...points, 2);
  }
  shape.dispose();
  flat.dispose();
  const glyphGeometry = own(new BufferGeometry());
  glyphGeometry.setAttribute('position', new BufferAttribute(new Float32Array(triangles), 3));
  for (const side of [1, -1]) {
    const material = own(new ShaderMaterial({
      uniforms: { face: { value: side } },
      vertexShader: 'uniform float face; void main(){vec2 p=position.xy;vec3 surface=vec3(face*p.x,p.y,face*sqrt(1.783*1.783-dot(p,p)));gl_Position=projectionMatrix*modelViewMatrix*vec4(surface,1.0);}',
      fragmentShader: 'void main(){gl_FragColor=vec4(0.0,0.0,0.0,1.0);}',
      side: 2
    }));
    const number = new Mesh(glyphGeometry, material);
    number.frustumCulled = false;
    ball.add(number);
  }
  ball.rotation.z = .12;
  ball.rotation.x = .1;
  spin.add(ball);
  axis.rotation.z = -.19;
  axis.rotation.x = .12;
  axis.add(spin);
  axis.position.set(5.1, .8, 0);
  axis.visible = false;
  left.position.set(-5.1, .8, 0);
  left.rotation.x = .3;
  group.add(left, axis);
  scene.add(anchor);
  scene.threeScene.add(group);

  let morph = -1, stretch = -1, disposed = false;
  function updateRing(ring, radius, y) {
    const { points, sides } = ring;
    ring.front.visible = ring.back.visible = radius > .0001;
    for (let col = 0; col <= columns; col++) {
      const angle = 2 * Math.PI * col / columns, c = Math.cos(angle), s = Math.sin(angle);
      for (let side = 0; side <= sides; side++) {
        const t = Math.PI * 2 * side / sides, r = radius + .012 * Math.cos(t), index = (col * (sides + 1) + side) * 3;
        points[index] = r * c;
        points[index + 1] = y + .012 * Math.sin(t);
        points[index + 2] = r * s;
      }
    }
    ring.geometry.attributes.position.needsUpdate = true;
  }
  function setMorph(value) {
    const next = Math.max(0, Math.min(1, value));
    if (next === morph || disposed) return;
    morph = next;
    for (let row = 0; row <= rows; row++) {
      const angle = Math.PI * (row / rows - .5), y = Math.sin(angle), c = Math.cos(angle);
      const radius = (1 - morph) * c + morph * Math.abs(y);
      const slope = morph === 1 ? Math.sign(y) : -(1 - morph) * y / Math.max(c, .00001) + morph * Math.sign(y);
      const scale = 1 / Math.hypot(1, slope);
      for (let col = 0; col <= columns; col++) {
        const theta = col * Math.PI * 2 / columns, cos = Math.cos(theta), sin = Math.sin(theta), index = (row * (columns + 1) + col) * 3;
        positions[index] = radius * cos;
        positions[index + 1] = y;
        positions[index + 2] = radius * sin;
        normals[index] = cos * scale;
        normals[index + 1] = -slope * scale;
        normals[index + 2] = sin * scale;
      }
    }
    surfaceGeometry.attributes.position.needsUpdate = true;
    surfaceGeometry.attributes.normal.needsUpdate = true;
    updateRing(rings[0], 1 - morph, 0);
    updateRing(rings[1], morph, 1);
    updateRing(rings[2], morph, -1);
  }
  function setStretch(value) {
    const next = Math.max(0, Math.min(1, value));
    if (next === stretch || disposed) return;
    stretch = next;
    left.scale.set(1.5 * (1 + .35 * stretch), 1.5, 1.5);
    left.rotation.z = -.18 * stretch;
  }
  setMorph(0);
  setStretch(0);
  return {
    anchor,
    setMorph,
    setStretch,
    setBallVisible(visible) { axis.visible = visible; },
    setSpin(phase) { spin.rotation.y = phase + .15; },
    dispose() {
      if (disposed) return;
      disposed = true;
      scene.threeScene.remove(group);
      scene.remove(anchor);
      anchor.dispose();
      for (const resource of resources) resource.dispose();
    }
  };
}
