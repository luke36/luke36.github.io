import wave

f = open("res.txt", "w") # 储存随机比特的文件
wf = wave.open("s1.wav", "rb") # 来源的音频. 这里是某节习题课的录音

bits = 0

magic_constant = 720 # 一秒内的取样数
sampwidth = wf.getsampwidth() # 音频的采样位数. 为了判断正负
framerate = wf.getframerate() # 音频的采样频率
step = framerate // magic_constant # 间隔
chunk_size = step * 16 # 一次读取的大小

data = wf.readframes(chunk_size)
while data[0] == 0:
    data = wf.readframes(chunk_size) # 这一段是清除一些音频前面的空白
while len(data) > 0:
    i = 0
    while i < len(data):
        cur = 0
        for k in range(0, sampwidth):
            cur <<= 8
            cur += data[i]
            i += 1 # 得出这一个取样点的数
        if (cur >= (1 << (8 * sampwidth - 1))): # 如果是负的
            f.write("1")
        else:
            f.write("0")
        i += step * sampwidth
        bits += 1
        print(bits) # 打印到目前为止生成的随机比特数量
    data = wf.readframes(chunk_size)
wf.close()
f.close()