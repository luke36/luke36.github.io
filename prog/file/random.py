import wave

f = open("res.txt", "w") # ����������ص��ļ�
wf = wave.open("s1.wav", "rb") # ��Դ����Ƶ. ������ĳ��ϰ��ε�¼��

bits = 0

magic_constant = 720 # һ���ڵ�ȡ����
sampwidth = wf.getsampwidth() # ��Ƶ�Ĳ���λ��. Ϊ���ж�����
framerate = wf.getframerate() # ��Ƶ�Ĳ���Ƶ��
step = framerate // magic_constant # ���
chunk_size = step * 16 # һ�ζ�ȡ�Ĵ�С

data = wf.readframes(chunk_size)
while data[0] == 0:
    data = wf.readframes(chunk_size) # ��һ�������һЩ��Ƶǰ��Ŀհ�
while len(data) > 0:
    i = 0
    while i < len(data):
        cur = 0
        for k in range(0, sampwidth):
            cur <<= 8
            cur += data[i]
            i += 1 # �ó���һ��ȡ�������
        if (cur >= (1 << (8 * sampwidth - 1))): # ����Ǹ���
            f.write("1")
        else:
            f.write("0")
        i += step * sampwidth
        bits += 1
        print(bits) # ��ӡ��ĿǰΪֹ���ɵ������������
    data = wf.readframes(chunk_size)
wf.close()
f.close()