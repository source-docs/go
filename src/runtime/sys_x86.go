// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build amd64 || 386

package runtime

import (
	"internal/goarch"
	"unsafe"
)

// adjust Gobuf as if it executed a call to fn with context ctxt
// and then stopped before the first instruction in fn.
func gostartcall(buf *gobuf, fn, ctxt unsafe.Pointer) {
	sp := buf.sp
	sp -= goarch.PtrSize
	*(*uintptr)(unsafe.Pointer(sp)) = buf.pc // 将 goexit 放到 sp - 1 的地方
	buf.sp = sp                              // fn 执行完会返回到这里
	buf.pc = uintptr(fn)                     // 将 buf.pc 设置为 fn, 从 fn 开始运行
	buf.ctxt = ctxt
}
