import { createDefectBound } from './stringy-defect-bound.js';
import { createClassGroup } from './stringy-class-group.js';

export function createComputing(slide) {
  return slide.matches('.defect-bound-slide') ? createDefectBound(slide) : createClassGroup(slide);
}
