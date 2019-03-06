CONTAINER_ID = xen_build_container
IMAGE_ID = xen_image

all:
	if docker ps -a | grep -wq $(CONTAINER_ID) ; then \
		docker rm xen_build_container ; \
	fi
	cd ../../ && docker build -t $(IMAGE_ID) -f integration/xen/Dockerfile .
	docker run -i -t --name $(CONTAINER_ID) $(IMAGE_ID) /bin/bash
