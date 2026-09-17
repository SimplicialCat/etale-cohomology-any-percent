#let crc32-table = {
  let tab = 256 * (0,)
  let crc32 = 1
  for b in range(7, -1, step: -1) {
    crc32 = crc32.bit-rshift(1).bit-xor(if (crc32.bit-and(1) != 0) {0xedb88320} else {0})
    let i = 1.bit-lshift(b)
    for j in range(0, 256, step: 2*i) {
      tab.at(i + j) = tab.at(j).bit-xor(crc32)
    }
  }
  tab
}

#let hash-crc32(val) = {
  if type(val) != bytes {
    if type(val) != str {
      val = repr(val)
    }
    val = bytes(val)
  }
  let crc32 = 0xffffffff
  for b in val {
    crc32 = crc32.bit-xor(b)
    crc32 = crc32.bit-rshift(8).bit-xor(crc32-table.at(crc32.bit-and(0xff)))
  }
  return crc32.bit-xor(0xffffffff)
}

#let hash-crc32-hex-str(val) = {
  let hash = hash-crc32(val)
  for i in range(8) {
    "0123456789abcdef".at(hash.bit-rshift(4 * (7 - i)).bit-and(0xf))
  }
}