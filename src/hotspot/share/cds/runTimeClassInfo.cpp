/*
 * Copyright (c) 2021, 2023, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "precompiled.hpp"
#include "cds/archiveBuilder.hpp"
#include "cds/dumpTimeClassInfo.hpp"
#include "cds/runTimeClassInfo.hpp"
#include "classfile/classFileStream.hpp"
#include "classfile/javaClasses.hpp"
#include "classfile/javaClasses.inline.hpp"
#include "classfile/systemDictionaryShared.hpp"
#include "classfile/vmSymbols.hpp"
#include "logging/log.hpp"
#include "logging/logStream.hpp"
#include "runtime/handles.inline.hpp"
#include "runtime/javaCalls.hpp"
#include "oops/oop.inline.hpp"
#if INCLUDE_AGGRESSIVE_CDS
#include "runtime/os.hpp"
#endif

void RunTimeClassInfo::init(DumpTimeClassInfo& info) {
  ArchiveBuilder* builder = ArchiveBuilder::current();
  builder->write_pointer_in_buffer(&_klass, info._klass);

  if (!SystemDictionaryShared::is_builtin(_klass)) {
    CrcInfo* c = crc();
    c->_clsfile_size = info._clsfile_size;
    c->_clsfile_crc32 = info._clsfile_crc32;
  }
  _num_verifier_constraints = info.num_verifier_constraints();
  _num_loader_constraints   = info.num_loader_constraints();
  int i;
  if (_num_verifier_constraints > 0) {
    RTVerifierConstraint* vf_constraints = verifier_constraints();
    char* flags = verifier_constraint_flags();
    for (i = 0; i < _num_verifier_constraints; i++) {
      vf_constraints[i]._name      = builder->any_to_offset_u4(info._verifier_constraints->at(i).name());
      vf_constraints[i]._from_name = builder->any_to_offset_u4(info._verifier_constraints->at(i).from_name());
    }
    for (i = 0; i < _num_verifier_constraints; i++) {
      flags[i] = info._verifier_constraint_flags->at(i);
    }
  }

  if (_num_loader_constraints > 0) {
    RTLoaderConstraint* ld_constraints = loader_constraints();
    for (i = 0; i < _num_loader_constraints; i++) {
      ld_constraints[i]._name = builder->any_to_offset_u4(info._loader_constraints->at(i).name());
      ld_constraints[i]._loader_type1 = info._loader_constraints->at(i).loader_type1();
      ld_constraints[i]._loader_type2 = info._loader_constraints->at(i).loader_type2();
    }
  }

  if (_klass->is_hidden()) {
    builder->write_pointer_in_buffer(nest_host_addr(), info.nest_host());
  }
  if (_klass->has_archived_enum_objs()) {
    int num = info.num_enum_klass_static_fields();
    set_num_enum_klass_static_fields(num);
    for (int i = 0; i < num; i++) {
      int root_index = info.enum_klass_static_field(i);
      set_enum_klass_static_field_root_index_at(i, root_index);
    }
  }

#if INCLUDE_AGGRESSIVE_CDS
  if (info.shared_class_file_size() != 0) {
    assert(_url_string == nullptr, "must assigned before _url_string");
    _shared_class_file = shared_class_file();
    memcpy(_shared_class_file, info.shared_class_file(), info.shared_class_file_size());
    ArchivePtrMarker::mark_pointer(&_shared_class_file);
    info.free_shared_class_file();
  } else {
    _shared_class_file = nullptr;
  }
  if (info.url_string_size() != 0) {
    _url_string = url_string();
    memcpy(_url_string, info.url_string(), info.url_string_size());
    ArchivePtrMarker::mark_pointer(&_url_string);
    info.free_url_string();
  } else {
    _url_string = nullptr;
  }
  set_classfile_timestamp(info.classfile_timestamp());
#endif // INCLUDE_AGGRESSIVE_CDS
}

size_t RunTimeClassInfo::crc_size(InstanceKlass* klass) {
  if (!SystemDictionaryShared::is_builtin(klass)) {
    return sizeof(CrcInfo);
  } else {
    return 0;
  }
}

#if INCLUDE_AGGRESSIVE_CDS
// check timestamp in the load time when UseAggressiveCDS.
//   regular_file(*.class): need to check timestamp.
//   jar_file(*.jar): no need to check timestamp here, already checked
//                    somewhere else, see SharedClassPathEntry::validate.
//   other_file: not supported when UseAggressiveCDS.
bool RunTimeClassInfo::check_classfile_timestamp(char* url_string, TRAPS) {
  if (SystemDictionaryShared::is_regular_file(url_string)) {
    ResourceMark rm(THREAD);
    char* dir = SystemDictionaryShared::get_filedir(url_string);
    if (dir == nullptr) {
      return false;
    }
    int64_t timestamp = SystemDictionaryShared::get_timestamp(dir, _klass->name());
    if (timestamp != _classfile_timestamp) {
      log_trace(cds, aggressive)("%s, timestamp mismatch: " INT64_FORMAT " -> " INT64_FORMAT,
                                  _klass->name()->as_C_string(),
                                  _classfile_timestamp, timestamp);
      return false;
    }
  } else if (!SystemDictionaryShared::is_jar_file(url_string)) {
    log_trace(cds, aggressive)("Unsupported URL:%s", url_string);
    return false;
  }
  return true;
}

Handle RunTimeClassInfo::get_protection_domain(Handle class_loader, TRAPS) {
  if (_url_string == nullptr) {
    return Handle();
  }
  char* data_ptr = (char*)(_url_string->data);

  if (CheckClassFileTimeStamp) {
    if (!check_classfile_timestamp(data_ptr, THREAD)) {
      return Handle();
    }
  }

  Handle url_string = java_lang_String::create_from_str(data_ptr, THREAD);
  JavaValue result(T_OBJECT);
  JavaCalls::call_virtual(&result,
                          class_loader,
                          class_loader->klass(),
                          vmSymbols::getProtectionDomainByURLString_name(),
                          vmSymbols::getProtectionDomainByURLString_signature(),
                          url_string, THREAD);
  if (!HAS_PENDING_EXCEPTION) {
    return Handle(THREAD, result.get_oop());
  } else {
    LogTarget(Warning, cds, aggressive) lt;
    if (lt.is_enabled()) {
      lt.print("Unknown exception in get_protection_domain():");
      ResourceMark rm(THREAD);
      Handle ex(THREAD, THREAD->pending_exception());
      CLEAR_PENDING_EXCEPTION;
      LogStream ls(lt);
      java_lang_Throwable::print_stack_trace(ex, &ls);
    } else {
      CLEAR_PENDING_EXCEPTION;
    }
  }
  return Handle();
}

ClassFileStream* RunTimeClassInfo::get_shared_class_file_stream() {
  if (_shared_class_file != nullptr) {
    return new ClassFileStream(_shared_class_file->data,
                               _shared_class_file->length,
                               "__VM_AggressiveCDS__",
                               ClassFileStream::verify);
  }
  return nullptr;
}
#endif // INCLUDE_AGGRESSIVE_CDS
