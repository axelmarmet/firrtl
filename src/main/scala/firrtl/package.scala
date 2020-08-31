// SPDX-License-Identifier: Apache-2.0

import firrtl.annotations.Annotation

package object firrtl {
  // Force initialization of the Forms object - https://github.com/freechipsproject/firrtl/issues/1462
  private val _dummyForms = firrtl.stage.Forms

  implicit def seqToAnnoSeq(xs: Seq[Annotation]) = AnnotationSeq(xs)
  implicit def annoSeqToSeq(as: AnnotationSeq): Seq[Annotation] = as.underlying

  /* Options as annotations compatibility items */
  @deprecated("Use firrtl.stage.TargetDirAnnotation", "FIRRTL 1.2")
  type TargetDirAnnotation = firrtl.options.TargetDirAnnotation

  @deprecated("Use firrtl.stage.TargetDirAnnotation", "FIRRTL 1.2")
  val TargetDirAnnotation = firrtl.options.TargetDirAnnotation

  type WRef = ir.Reference
  type WSubField = ir.SubField
  type WSubIndex = ir.SubIndex
  type WSubAccess = ir.SubAccess
  type WDefInstance = ir.DefInstance

  @deprecated("Use firrtl.backends.verilog.VerilogEmitter", "FIRRTL 1.4")
  type VerilogEmitter = firrtl.backends.verilog.VerilogEmitter
  @deprecated("Use firrtl.backends.verilog.VerilogEmitter", "FIRRTL 1.4")
  val VerilogEmitter = firrtl.backends.verilog.VerilogEmitter
  @deprecated("Use firrtl.backends.verilog.MinimumVerilogEmitter", "FIRRTL 1.4")
  type MinimumVerilogEmitter = firrtl.backends.verilog.MinimumVerilogEmitter
  @deprecated("Use firrtl.backends.verilog.SystemVerilogEmitter", "FIRRTL 1.4")
  type SystemVerilogEmitter = firrtl.backends.verilog.SystemVerilogEmitter
  @deprecated("Use firrtl.backends.firrtl.FirrtlEmitter", "FIRRTL 1.4")
  type FirrtlEmitter = firrtl.backends.firrtl.FirrtlEmitter
  @deprecated("Use firrtl.backends.firrtl.ChirrtlEmitter", "FIRRTL 1.4")
  type ChirrtlEmitter = firrtl.backends.firrtl.ChirrtlEmitter
  @deprecated("Use firrtl.backends.firrtl.HighFirrtlEmitter", "FIRRTL 1.4")
  type HighFirrtlEmitter = firrtl.backends.firrtl.HighFirrtlEmitter
  @deprecated("Use firrtl.backends.firrtl.MiddleFirrtlEmitter", "FIRRTL 1.4")
  type MiddleFirrtlEmitter = firrtl.backends.firrtl.MiddleFirrtlEmitter
  @deprecated("Use firrtl.backends.firrtl.LowFirrtlEmitter", "FIRRTL 1.4")
  type LowFirrtlEmitter = firrtl.backends.firrtl.LowFirrtlEmitter
}
